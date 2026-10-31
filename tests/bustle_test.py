"""BUSTLE's value semantics, learned scheduling, and real Aeon integration."""

from __future__ import annotations

import json
import subprocess
import sys
import time
from pathlib import Path

import pytest

from aeon.core.terms import Application, Var
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.modules.bustle import BustleSynthesizer
from aeon.synthesis.modules.bustle.model import GuidanceModel
from aeon.synthesis.modules.bustle.search import Operation, SearchStats, Value, enumerate_values
from aeon.synthesis.modules.bustle.signatures import (
    FEATURE_COUNT,
    aggregate,
    pair_signature,
    probability_penalty,
    task_signature,
    unary_signature,
    value_signature,
)
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.name import Name
from tests.driver import check_and_return_core

from aeon.synthesis.modules.bustle.values import MAX_DEPTH, MAX_NODES, depth, identity, nodes, valid_value

ROOT = Path(__file__).resolve().parents[1]


def test_signature_trits_and_type_absence():
    assert aggregate([True, True]) == 1
    assert aggregate([False, False]) == -1
    assert aggregate([True, False]) == 0
    assert aggregate([]) == 2
    assert unary_signature([True, False])[:5] == (2,) * 5  # Bool is not Int.
    strings = pair_signature(["abc", "xy"], ["abc_", "XYZ"])
    assert strings[5] == 0  # substring: true for one example only
    assert strings[9] == 1  # case-insensitive substring: true for both
    assert pair_signature([1, 2], [True, False]) == (2,) * len(strings)
    with pytest.raises(ValueError, match="equal example counts"):
        pair_signature([1], [1, 2])


def test_features_preserve_multiple_input_columns():
    columns = [("abc", "xy"), (1, 2)]
    output = ("abc_", "XY")
    task = task_signature(columns, output)
    signature = task + value_signature(("ABC", "XY"), output)
    assert len(signature) == FEATURE_COUNT
    assert task != task_signature(list(reversed(columns)), output)


@pytest.mark.parametrize(
    "probability,penalty", [(0, 5), (0.099, 5), (0.1, 4), (0.2, 3), (0.3, 2), (0.4, 1), (0.6, 0), (1, 0)]
)
def test_paper_probability_bins(probability, penalty):
    assert probability_penalty(probability) == penalty


@pytest.mark.parametrize("probability", [float("nan"), float("inf"), -0.1, 1.1])
def test_invalid_model_probabilities_fail(probability):
    with pytest.raises(ValueError, match="probabilities"):
        probability_penalty(probability)


def _op(name, function):
    return Operation(Var(Name(name, 0)), ("Int",), "Int", lambda arguments: function(arguments[0]))


def _enumerate(atoms, operations, *, accept=lambda value: False, predict=None, **kwargs):
    stats = SearchStats()
    result = enumerate_values(
        atoms,
        operations,
        [(0, 1)],
        (20, 21),
        accept=accept,
        predict=predict,
        deadline=time.monotonic() + 5,
        stats=stats,
        **kwargs,
    )
    return result, stats


def test_observational_equivalence_is_over_all_examples():
    atoms = [Value(Var(Name("x", 0)), "Int", (0, 1))]
    operations = [_op("same", lambda x: x), _op("different", lambda x: x * 2)]
    _, stats = _enumerate(atoms, operations, max_weight=2)
    assert stats.duplicates == 1
    assert {v.outputs for v in stats.values} == {(0, 1), (0, 2)}


def test_guidance_changes_child_weights_and_search_order():
    atoms = [Value(Var(Name("x", 0)), "Int", (0, 1))]
    operations = [_op("increment", lambda x: x + 1)]

    def accepts(value):
        return value.outputs == (2, 3)

    unguided, baseline = _enumerate(atoms, operations, accept=accepts, max_weight=3)
    # A low usefulness probability postpones x+1 from weight 2 to weight 7,
    # so composing another increment becomes possible only at weight 8.
    result, postponed = _enumerate(
        atoms, operations, accept=accepts, predict=lambda features: [0.0] * len(features), max_weight=3
    )
    assert unguided is not None and result is None
    assert baseline.final_weight == 3
    assert postponed.model_calls > 0 and postponed.reweighted == 1
    assert postponed.values[-1].weight == 7
    result, _ = _enumerate(
        atoms, operations, accept=accepts, predict=lambda features: [0.0] * len(features), max_weight=8
    )
    assert result is not None and result.weight == 8


def test_batched_guidance_and_leaves_remain_at_weight_one():
    atoms = [Value(Var(Name("x", 0)), "Int", (0, 1))]
    batches = []

    def predict(features):
        batches.append(features)
        return [1.0] * len(features)

    _, stats = _enumerate(
        atoms, [_op("add1", lambda x: x + 1), _op("add2", lambda x: x + 2)], predict=predict, max_weight=2
    )
    assert stats.values[0].weight == 1
    assert len(batches) == 1 and len(batches[0]) == 2
    assert all(len(feature) == FEATURE_COUNT for feature in batches[0])


def test_deadline_and_value_cap_stop_search():
    atoms = [Value(Var(Name("x", 0)), "Int", (0, 1))]
    result, stats = _enumerate(atoms, [_op("increment", lambda x: x + 1)], max_values=2)
    assert result is None and stats.stopped == "value limit"
    stats = SearchStats()
    assert (
        enumerate_values(atoms, [], [(0, 1)], (20, 21), accept=lambda v: False, predict=None, deadline=0, stats=stats)
        is None
    )
    assert stats.stopped == "budget"


def test_runtime_errors_and_wrong_scalar_types_are_discarded():
    atoms = [Value(Var(Name("x", 0)), "Int", (0, 1))]
    operations = [_op("divide", lambda x: 1 // x), _op("wrong", lambda x: True), _op("increment", lambda x: x + 1)]
    result, stats = _enumerate(atoms, operations, accept=lambda v: v.outputs == (1, 2), max_weight=2)
    assert result is not None
    assert stats.invalid == 2


def test_rejected_representative_does_not_hide_a_valid_solution():
    atoms = [Value(Var(Name("x", 0)), "Int", (0, 1))]
    operations = [_op("rejected", lambda x: x + 1), _op("accepted", lambda x: x + 1)]

    def accept(value):
        return isinstance(value.term, Application) and value.term.fun == Var(Name("accepted", 0))

    result, _ = _enumerate(atoms, operations, accept=accept, max_weight=2)
    assert result is not None and result.term.fun == Var(Name("accepted", 0))


def test_trained_checkpoint_roundtrip_and_stdlib_inference(tmp_path, monkeypatch):
    from aeon.synthesis.modules.bustle import model as model_module

    model = GuidanceModel.load()
    assert model.provenance["trained"]
    assert model.provenance["final_training_loss"] < model.provenance["initial_training_loss"]
    features = [task_signature([(1, 2)], (2, 3)) + value_signature(values, (2, 3)) for values in [(1, 2), (99, 99)]]
    accelerated = model.predict(features)
    assert abs(accelerated[0] - accelerated[1]) > 0.01
    checkpoint = tmp_path / "guidance.json"
    model.save(checkpoint)
    monkeypatch.setattr(model_module, "np", None)
    pure_python = GuidanceModel.load(checkpoint).predict(features)
    assert list(accelerated) == pytest.approx(pure_python, abs=1e-12)
    data = json.loads(checkpoint.read_text())
    data["signature_version"] = -1
    checkpoint.write_text(json.dumps(data))
    with pytest.raises(ValueError, match="schema"):
        GuidanceModel.load(checkpoint)


def test_training_reduces_loss_without_using_benchmark_examples():
    pytest.importorskip("numpy")
    from aeon.synthesis.modules.bustle.train import train

    model = train(searches=10, epochs=8, seed=4)
    assert model.provenance["training_rows"] > 0
    assert model.provenance["validation_rows"] > 0
    assert model.provenance["final_training_loss"] < model.provenance["initial_training_loss"]


def _solve(source, synthesizer=None):
    term, ctx, evaluation_ctx, metadata = check_and_return_core(source)
    targets = incomplete_functions_and_holes(ctx, term)
    synthesizer = synthesizer or BustleSynthesizer()
    holes = synthesize_holes(
        ctx, evaluation_ctx, term, targets, metadata, synthesizer, budget=5, ui=SilentSynthesisUI()
    )
    assert all(body is not None for body in holes.values())
    return synthesizer


def test_factory_and_baseline_are_registered():
    assert isinstance(make_synthesizer("bustle"), BustleSynthesizer)
    assert make_synthesizer("bustle").guided
    assert not make_synthesizer("bustle_baseline").guided


@pytest.mark.parametrize("guided", [True, False])
def test_two_argument_integer_synthesis(guided):
    backend = _solve(
        """
        @example(add 2 5 = 7)
        @example(add 7 1 = 8)
        @example(add 3 9 = 12)
        def add (x:Int) (y:Int) : Int := ?sum;
    """,
        BustleSynthesizer(guided=guided),
    )
    assert backend.stats.stopped == "solution"


def test_string_composition_uses_trained_guidance_and_passes_examples():
    driver = AeonDriver(
        AeonConfig(synthesizer="bustle", synthesis_ui=SilentSynthesisUI(), synthesis_budget=5, no_main=True)
    )
    assert list(driver.parse(filename=str(ROOT / "examples/synthesis/bustle/string.ae"))) == []
    assert driver.has_synth()
    driver.synth()
    assert not driver.has_synth()
    assert driver.run_tests() == []
    backend = _solve((ROOT / "examples/synthesis/bustle/string.ae").read_text())
    assert backend.stats.model_calls > 0

    # This easy string task assigns no penalty to the useful early values.
    # A compound arithmetic task must also penalize distractors with the actual
    # bundled model, rather than just exercising a mocked predictor.
    numeric = _solve("@example(f 2 = 5)\n@example(f 5 = 11)\n@example(f 9 = 19)\ndef f (x:Int) : Int := ?hole;")
    assert numeric.stats.reweighted > 0


def test_float_csv_is_rejected_as_outside_the_paper_dsl():
    with pytest.raises(SynthesisNotSuccessful, match="result must be Int, Bool, or String"):
        _solve('@csv_data("1,2\\n4,5\\n9,10")\ndef succ (x:Float) : Float := ?succ;')


def test_conditional_synthesis():
    _solve("""
        @example(sign 0 = 0)
        @example(sign 1 = 0)
        @example(sign 2 = 1)
        @example(sign 3 = 1)
        def sign (x:Int) : Int := ?sign;
    """)


def test_typechecker_rejects_example_consistent_but_invalid_refinement():
    with pytest.raises(SynthesisNotSuccessful, match="well-typed"):
        _solve(
            """
            @example(bad 1 = 1)
            @example(bad 2 = 2)
            def bad (x:Int) : {v:Int | v > 10} := ?bad;
        """,
            BustleSynthesizer(guided=False, max_weight=3),
        )


def test_missing_examples_and_bad_checkpoint_fail_clearly(tmp_path):
    with pytest.raises(SynthesisNotSuccessful, match="needs an output refinement"):
        _solve("def f (x:Int) : Int := ?hole;")
    with pytest.raises(SynthesisNotSuccessful, match="cannot load trained guidance"):
        _solve("@example(f 1 = 2)\ndef f (x:Int) : Int := ?hole;", BustleSynthesizer(tmp_path / "missing.json"))


def test_extra_objectives_are_not_silently_ignored():
    with pytest.raises(SynthesisNotSuccessful, match="additional optimization"):
        _solve("""
            @example(f 1 = 2)
            @minimize_int(f 0)
            def f (x:Int) : Int := ?hole;
        """)


def test_cli_exposes_and_executes_bustle():
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "aeon",
            "--no-main",
            "--budget",
            "5",
            "-s",
            "bustle",
            "examples/synthesis/bustle/string.ae",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert "?clean:" in result.stdout
    assert "upper" in result.stdout and "trim" in result.stdout


def test_default_backend_works_without_numpy():
    source = """
import sys
sys.modules['numpy'] = None
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.synthesis.modules.bustle import model
assert model.np is None
config = AeonConfig(synthesizer='bustle', synthesis_ui=SilentSynthesisUI(), synthesis_budget=5, no_main=True)
driver = AeonDriver(config)
assert not list(driver.parse(filename='examples/synthesis/bustle/string.ae'))
assert driver.has_synth()
driver.synth()
assert not driver.has_synth()
assert not driver.run_tests()
"""
    process = subprocess.run([sys.executable, "-c", source], cwd=ROOT, capture_output=True, text=True, timeout=30)
    assert process.returncode == 0, process.stdout + process.stderr


def test_adt_depth_constructor_identity_and_full_structural_observations():
    first = ("Tree_node", ("Tree_leaf", 1), ("Tree_leaf", 2))
    second = ("Tree_node", ("Tree_leaf", 9), ("Tree_leaf", 2))
    assert depth(first) == depth(second) == 2
    assert nodes(first) == 3
    assert identity(first) != identity(second)
    assert identity(("Box_box", True)) != identity(("Box_box", 1))
    signature = pair_signature([first], [second])
    assert signature[15] == -1  # Full structural identity differs.
    assert signature[16] == 1  # Root constructor identity agrees.
    assert signature[17] == 1  # Depth agrees.
    assert unary_signature([first])[-5:] == (-1, 1, 1, 1, 1)


def test_adt_validation_checks_tags_fields_types_and_structural_bounds():
    schemas = {"Chain": {"Chain_nil": (), "Chain_cons": ("Int", "Chain")}}
    nil = ("Chain_nil",)
    assert valid_value(("Chain_cons", 3, nil), "Chain", schemas)
    for malformed in [("Other_nil",), ("Chain_cons", 3), ("Chain_cons", True, nil), ("Chain_cons", 3, [])]:
        assert not valid_value(malformed, "Chain", schemas)
    chain = nil
    for _ in range(MAX_DEPTH):
        chain = ("Chain_cons", 1, chain)
    assert not valid_value(chain, "Chain", schemas)
    tree_schemas = {"Tree": {"Tree_leaf": (), "Tree_node": ("Tree", "Tree")}}
    tree = ("Tree_leaf",)
    for _ in range(7):
        tree = ("Tree_node", tree, tree)
    assert nodes(tree) > MAX_NODES
    assert not valid_value(tree, "Tree", tree_schemas)
    assert not valid_value(("native_model",), "Opaque", {})


def test_same_depth_and_constructor_do_not_merge_different_payloads():
    schemas = {"Box": {"Box_box": ("Int",)}}
    atoms = [
        Value(Var(Name("a", 0)), "Box", (("Box_box", 1), ("Box_box", 2))),
        Value(Var(Name("b", 0)), "Box", (("Box_box", 3), ("Box_box", 4))),
    ]
    _, stats = _enumerate(atoms, [], max_weight=1, valid=lambda v, k: valid_value(v, k, schemas))
    assert stats.unique == 2


@pytest.mark.parametrize("backend", ["bustle", "bustle_baseline"])
@pytest.mark.parametrize("example", ["list.ae", "tree.ae"])
def test_adt_constructor_synthesis_passes_real_examples(backend, example):
    driver = AeonDriver(
        AeonConfig(synthesizer=backend, synthesis_ui=SilentSynthesisUI(), synthesis_budget=5, no_main=True)
    )
    assert not list(driver.parse(filename=str(ROOT / "examples/synthesis/bustle" / example)))
    assert driver.has_synth()
    driver.synth()
    assert not driver.has_synth()
    assert not driver.run_tests()


def _solve_adt_file(tmp_path, source):
    path = tmp_path / "adt.ae"
    path.write_text(source)
    driver = AeonDriver(
        AeonConfig(synthesizer="bustle", synthesis_ui=SilentSynthesisUI(), synthesis_budget=5, no_main=True)
    )
    assert not list(driver.parse(filename=str(path)))
    assert driver.has_synth()
    driver.synth()
    assert not driver.has_synth()
    assert not driver.run_tests()
    return driver


def test_adt_to_scalar_synthesis_with_first_order_observer(tmp_path):
    _solve_adt_file(
        tmp_path,
        """
        inductive Box
        | mk (value:Int) : Box
        def read (b:Box) : Int := match b with | .mk value => value;
        @example(unbox (Box.mk 4) = 4)
        @example(unbox (Box.mk 7) = 7)
        def unbox (b:Box) : Int := ?unbox;
    """,
    )


def test_parametric_adt_constructor_synthesis(tmp_path):
    _solve_adt_file(
        tmp_path,
        """
        inductive Box a
        | mk (value:a) : (Box a)
        @example(wrap 4 = Box.mk 4)
        @example(wrap 7 = Box.mk 7)
        def wrap (x:Int) : (Box Int) := ?wrap;
    """,
    )


def test_parametric_nullary_constructor_can_seed_a_result(tmp_path):
    _solve_adt_file(
        tmp_path,
        """
        inductive Chain a
        | nil : (Chain a)
        | cons (head:a) (tail:(Chain a)) : (Chain a)
        @example(single 4 = Chain.cons 4 Chain.nil)
        @example(single 7 = Chain.cons 7 Chain.nil)
        def single (x:Int) : (Chain Int) := ?single;
    """,
    )


def test_constructor_example_extractor_rejects_nonconstructor_calls(tmp_path):
    path = tmp_path / "unsupported.ae"
    path.write_text("""
        inductive Box
        | mk (value:Int) : Box
        def make (x:Int) : Box := Box.mk x;
        @example(f 1 = make 1)
        def f (x:Int) : Box := ?f;
    """)
    driver = AeonDriver(
        AeonConfig(synthesizer="bustle", synthesis_ui=SilentSynthesisUI(), synthesis_budget=5, no_main=True)
    )
    assert not list(driver.parse(filename=str(path)))
    assert not any(entry.get("constructor_io_examples") for entry in driver.metadata.values())
