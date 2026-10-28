from pathlib import Path

import pytest

from aeon.core.terms import Var
from aeon.core.types import t_unit, top
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.api import UnsupportedSynthesisGoal
from aeon.synthesis.fitness_eval import set_program_tail
from aeon.synthesis.identification import get_holes_info
from aeon.synthesis.refinement_examples import derive_refinement_examples
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.backend.evaluator import eval as evaluate

EXAMPLE = Path(__file__).resolve().parents[1] / "examples/synthesis/nand_full_adder.ae"
NINE_NANDS = """let g1 := nand a b in
let g2 := nand a g1 in
let g3 := nand b g1 in
let g4 := nand g2 g3 in
let g5 := nand g4 carry_in in
let g6 := nand g4 g5 in
let g7 := nand carry_in g5 in
let sum := nand g6 g7 in
let carry_out := nand g1 g5 in
AdderOutput.mk sum carry_out"""


def driver(source, backend="decision_tree", budget=5):
    d = AeonDriver(AeonConfig(backend, SilentSynthesisUI(), budget, no_main=True))
    assert not list(d.parse(aeon_code=source))
    d.has_synth()
    return d


def samples(d, **kwargs):
    return derive_refinement_examples(d.typing_ctx, d.core, d.incomplete_functions[0][0], budget=5, **kwargs)


def test_refinement_examples_cover_dependent_numeric_inputs():
    d = driver("""def f (x:{x:Int | 0 <= x && x <= 2}) (y:{y:Int | x <= y && y <= 2}) :
        {r:Int | r = x + y} := ?h;""")
    with d.session.activate():
        data = samples(d)
        assert sorted(data["training_data"]) == [[x, y, x + y] for x in range(3) for y in range(x, 3)]
        assert data["refinement_examples_unique"]
        assert data["refinement_examples_complete"]
        assert not d.metadata  # No source decorators or metadata mutation.


def test_decision_tree_synthesizes_from_refinement_without_examples():
    d = driver("""def f (x:{x:Int | 0 <= x && x <= 3}) :
        {r:Int | (x < 2 && r = 0) || (x >= 2 && r = 1)} := ?h;""")
    with d.session.activate():
        d.synth()
        f = evaluate(set_program_tail(d.core, Var(d.incomplete_functions[0][0])), d.evaluation_ctx)
        assert [f(i) for i in range(4)] == [0, 0, 1, 1]


def test_explicit_examples_are_preserved(monkeypatch):
    d = driver("@example(f 1 = 2)\ndef f (x:Int) : Int := ?h;")
    before = {name: dict(entry) for name, entry in d.metadata.items()}

    def forbidden(*args, **kwargs):
        raise AssertionError("Explicit examples must not trigger inference")

    monkeypatch.setattr("aeon.synthesis.entrypoint.derive_refinement_examples", forbidden)
    with d.session.activate():
        d.synth()
    assert d.metadata == before


def test_nonunique_outputs_are_not_fabricated_exact_labels():
    d = driver("def f (x:{x:Int | x = 0}) : {r:Int | r >= x} := ?h;")
    with d.session.activate():
        data = samples(d)
        assert not data["refinement_examples_unique"]
        assert "training_data" not in data and "io_examples" not in data
        assert data["refinement_example_matches"]((0,))
        assert data["refinement_example_matches"]((10,))
        assert not data["refinement_example_matches"]((-1,))
        with pytest.raises(UnsupportedSynthesisGoal, match="uniquely determined numeric output"):
            d.synth()


def test_missing_output_refinement_is_explicit():
    d = driver("def f (x:Int) : Int := ?h;")
    with d.session.activate(), pytest.raises(UnsupportedSynthesisGoal, match="output refinement"):
        samples(d)


def test_unbounded_input_corpus_is_capped():
    d = driver("def f (x:Int) : {r:Int | r = x + 1} := ?h;")
    with d.session.activate():
        data = samples(d, max_examples=5)
        assert len(data["training_data"]) == 5
        assert not data["refinement_examples_complete"]


def test_nand_refinement_generates_eight_inputs_without_fixing_depth():
    d = driver(EXAMPLE.read_text())
    with d.session.activate():
        data = samples(d)
        rows = data["refinement_examples"]
        assert len(rows) == 8 and data["refinement_examples_complete"]
        assert not data["refinement_examples_unique"]
        assert "constructor_io_examples" not in data
        assert len({tuple(args) for args, _ in rows}) == 8
        varied_depth_outputs = []
        for args, out in rows:
            assert all(arg[1] == 0 for arg in args)
            total = sum(arg[0] == "Bit_high" for arg in args)
            assert (out[1][0] == "Bit_high") + 2 * (out[2][0] == "Bit_high") == total
            varied_depth_outputs.append(("AdderOutput_mk", (out[1][0], 6), (out[2][0], 5)))
        assert data["refinement_example_matches"](tuple(varied_depth_outputs))
        wrong = list(varied_depth_outputs)
        _, a, b = wrong[0]
        wrong[0] = ("AdderOutput_mk", ("Bit_high" if a[0] == "Bit_low" else "Bit_low", a[1]), b)
        assert not data["refinement_example_matches"](tuple(wrong))


def test_nand_scope_excludes_depth_forging_and_logical_shortcuts():
    d = driver(EXAMPLE.read_text(), "gp")
    with d.session.activate():
        info = get_holes_info(d.typing_ctx, d.core, top, targets=d.incomplete_functions, refined_types=True)
        _, ctx = next(iter(info.values()))
        names = {n.name: ty for n, ty in ctx.concrete_vars()}
        for name in (
            "logical_not",
            "logical_and",
            "at_depth",
            "bit_depth",
            "Bit_low",
            "Bit_high",
            "Bit_rec",
            "Bit_value",
            "Bit_depth",
            "AdderOutput_rec",
            "AdderOutput_sum_value",
            "AdderOutput_carry_value",
            "full_adder",
        ):
            assert names[name] == t_unit, name


def test_nand_objective_distinguishes_depth_and_correctness():
    for circuit, expected_depth in (
        (NINE_NANDS, 6),
        (
            NINE_NANDS.replace(
                "AdderOutput.mk sum carry_out", "AdderOutput.mk (nand (nand sum sum) (nand sum sum)) carry_out"
            ),
            8,
        ),
    ):
        d = driver(EXAMPLE.read_text().replace("?circuit", circuit), "gp")
        with d.session.activate():
            goals = [g for entry in d.metadata.values() for g in entry.get("goals", [])]
            assert len(goals) == 1 and goals[0].minimize
            assert evaluate(set_program_tail(d.core, Var(goals[0].function)), d.evaluation_ctx) == expected_depth
    bad = EXAMPLE.read_text().replace(
        "?circuit", NINE_NANDS.replace("AdderOutput.mk sum carry_out", "AdderOutput.mk sum sum")
    )
    d = AeonDriver(AeonConfig("gp", SilentSynthesisUI(), 1, no_main=True))
    assert list(d.parse(aeon_code=bad))


@pytest.mark.parametrize("backend", ["contata", "bustle_baseline"])
def test_example_driven_backends_use_generated_exact_labels(backend):
    d = driver("def f (x:{x:Int | 0 <= x && x <= 2}) : {r:Int | r = x + 1} := ?h;", backend)
    with d.session.activate():
        d.synth()
        f = evaluate(set_program_tail(d.core, Var(d.incomplete_functions[0][0])), d.evaluation_ctx)
        assert [f(i) for i in range(3)] == [1, 2, 3]


def test_bustle_accepts_nonunique_refinement_observations():
    d = driver("def f (x:{x:Int | 0 <= x && x <= 2}) : {r:Int | r >= x} := ?h;", "bustle_baseline")
    with d.session.activate():
        d.synth()
        f = evaluate(set_program_tail(d.core, Var(d.incomplete_functions[0][0])), d.evaluation_ctx)
        assert all(f(i) >= i for i in range(3))


def test_decision_tree_negative_integer_split_from_refinement():
    d = driver("""def f (x:{x:Int | (-2) <= x && x <= 1}) :
        {r:Int | (x < (-1) && r = 0) || (x >= (-1) && r = 1)} := ?h;""")
    with d.session.activate():
        d.synth()
        f = evaluate(set_program_tail(d.core, Var(d.incomplete_functions[0][0])), d.evaluation_ctx)
        assert [f(i) for i in range(-2, 2)] == [0, 1, 1, 1]


def test_refinement_string_examples_decode_unicode():
    d = driver('def f (s:{s:String | s = "λ"}) : {r:String | r = s} := ?h;', "bustle_baseline")
    with d.session.activate():
        data = samples(d)
        assert data["io_examples"] == [(["λ"], "λ")]
        d.synth()


def test_unsatisfiable_refinement_does_not_invent_examples():
    from aeon.synthesis.api import SynthesisNotSuccessful

    d = driver("def f (x:Int) : {r:Int | r > x && r < x} := ?h;")
    with d.session.activate(), pytest.raises(SynthesisNotSuccessful, match="No checked refinement examples"):
        samples(d)


def test_nullary_refinement_synthesizes_constant():
    d = driver("def f : {r:Int | r = 7} := ?h;")
    with d.session.activate():
        d.synth()
        assert evaluate(set_program_tail(d.core, Var(d.incomplete_functions[0][0])), d.evaluation_ctx) == 7


def test_nested_hole_does_not_receive_function_output_as_its_label():
    d = driver("def f (x:Int) : {r:Int | r = x + 2} := 1 + (?h : {y:Int | y = x + 1});")
    with d.session.activate(), pytest.raises(UnsupportedSynthesisGoal, match="result position"):
        samples(d)


def test_local_hole_does_not_receive_another_holes_output_labels():
    d = driver("""def f (x:Int) : {r:Int | r = x + 2} :=
        let y : {y:Int | y = x + 1} := ?inner in ?result;""")
    inner = next(name for name in d.incomplete_functions[0][1] if name.name == "inner")
    with d.session.activate(), pytest.raises(UnsupportedSynthesisGoal, match="result position"):
        samples(d, hole_name=inner)
