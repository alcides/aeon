"""Specification combinations in bounded Boolean, grammar, and LLM search."""

import pytest
from pathlib import Path

from aeon.core.terms import Literal
from aeon.core.types import t_int
from aeon.synthesis.decorators import Example, Goal
from aeon.synthesis.api import SynthesisNotSuccessful, UnsupportedSynthesisGoal
from aeon.synthesis.modules.amaze.synthesizer import AmazeSynthesizer
from aeon.synthesis.modules.boolean_bounded import BooleanBoundedSynthesizer
from aeon.synthesis.modules.dp_gp import DPSynthesizer
from aeon.synthesis.modules.dp_gp.model import Config as DPConfig
from aeon.synthesis.modules.llm.specifications import specification_prompt
from aeon.synthesis.modules.type_constrained import TypeConstrainedSynthesizer
from aeon.utils.name import Name
from tests.boolean_bounded_test import call
from tests.joint_hole_synthesis_test import fill, parse, solve
from tests.synthesis_specifications_test import solve as solve_source
from tests.type_constrained_synthesizer_test import Attempts


@pytest.mark.parametrize("direction,expected", [("minimize", True), ("maximize", False)])
def test_boolean_bounds_enumerate_beyond_first_feasible_model(direction, expected):
    driver = parse(f"""
        @bounded_cnf(1)
        @{direction}_int(if f then 0 else 1)
        def f:Bool := ?body;
    """)
    backend = BooleanBoundedSynthesizer()
    completed = fill(driver, solve(driver, backend, budget=5))
    assert call(driver, completed, "f") is expected
    assert len(backend.pareto_front) == 1
    assert backend.report.iterations >= 3


def test_boolean_pareto_front_is_transported_out_of_worker():
    driver = parse("""
        @bounded_cnf(1)
        @minimize_int(if f then 0 else 1)
        @maximize_int(if f then 0 else 1)
        def f:Bool := ?body;
    """)
    backend = BooleanBoundedSynthesizer()
    fill(driver, solve(driver, backend, budget=5))
    assert {tuple(scores) for scores, _ in backend.pareto_front} == {(0.0, 0.0), (1.0, 1.0)}


@pytest.mark.parametrize("file", [False, True])
def test_boolean_csv_rejection_continues_selector_search(file, tmp_path):
    data = tmp_path / "boolean.csv"
    data.write_text("true,false\nfalse,true\n")
    decorator = f'@csv_file("{data}")' if file else r'@csv_data("true,false\nfalse,true")'
    driver = parse(f"@bounded_cnf(1) {decorator} def f(x:Bool):Bool := ?body;")
    backend = BooleanBoundedSynthesizer()
    completed = fill(driver, solve(driver, backend, budget=5))
    assert call(driver, completed, "f", True) is False
    assert call(driver, completed, "f", False) is True
    assert backend.report.rejected_candidates > 0


def test_impossible_boolean_csv_exhausts_finite_selectors():
    driver = parse(r'@bounded_cnf(1) @csv_data("true,false\ntrue,true") def f(x:Bool):Bool := ?body;')
    with pytest.raises(SynthesisNotSuccessful, match="bounded_unsat"):
        solve(driver, BooleanBoundedSynthesizer(), budget=5)


def test_boolean_size_and_examples_use_shared_acceptance_and_scoring():
    driver = parse("""
        @bounded_cnf(1)
        @minimize_size
        @example(f false = true)
        def f(x:Bool):Bool := ?body;
        @property(2) def law(x:Bool):Bool := f false;
    """)
    backend = BooleanBoundedSynthesizer()
    completed = fill(driver, solve(driver, backend, budget=5))
    assert call(driver, completed, "f", True) is True
    assert call(driver, completed, "f", False) is True
    assert backend.pareto_front
    assert all(isinstance(term.terms[0], Literal) for _, term in backend.pareto_front)


def test_both_llm_adapters_share_all_specification_hints():
    target = Name("f", 1)
    metadata = {
        target: {
            "doc": "Return an accurate small implementation.",
            "examples": [Example(Name("example", 2), "f 1 = 2")],
            "csv_examples": [([1.0], 2.0), ([2.0], 3.0)],
            "goals": [
                Goal(True, 1, target, "size"),
                Goal(False, 2, Name("quality", 3)),
                Goal(True, 1, Name("law", 4), "property"),
                Goal(True, 1, Name("measure", 5), "cputime"),
                Goal(True, 1, Name("energy", 6), "energy"),
            ],
            "specification_sources": ["def quality := ..."],
        }
    }
    prompt = specification_prompt(metadata, target)
    for expected in (
        "f 1 = 2",
        "(2.0,) = 3.0",
        "expression size",
        "Maximize",
        "law",
        "CPU time",
        "energy",
        "def quality",
    ):
        assert expected in prompt
    assert prompt.endswith(metadata[target]["doc"])


@pytest.mark.parametrize("file", [False, True])
def test_type_constrained_llm_uses_csv_loss_and_prompt(file, tmp_path, monkeypatch):
    monkeypatch.setenv("AEON_TC_ATTEMPTS", "2")
    csv = tmp_path / "data.csv"
    csv.write_text("0.0,1.0\n1.0,1.0\n")
    decorator = f'@csv_file("{csv}")' if file else r'@csv_data("0.0,1.0\n1.0,1.0")'
    adapter = Attempts(["0.0", "1.0"])
    backend = TypeConstrainedSynthesizer(adapter_factory=lambda: adapter)
    result = solve_source(f"{decorator} def f(x:Float):Float := ?body;", backend, budget=10)
    assert next(iter(result.values())).value == 1.0
    assert "CSV input/output observations" in adapter.prompts[0]


def test_type_constrained_size_combines_with_refinement_and_example(monkeypatch):
    monkeypatch.setenv("AEON_TC_ATTEMPTS", "2")
    adapter = Attempts(["1 + 0", "1"])
    backend = TypeConstrainedSynthesizer(adapter_factory=lambda: adapter)
    result = solve_source("@minimize_size @example(f 0 = 1) def f(x:Int):{v:Int | v > 0} := ?body;", backend, budget=10)
    assert next(iter(result.values())) == Literal(1, t_int)
    assert backend.pareto_front
    assert len(backend.pareto_front) == 1


def test_amaze_supports_size_with_examples_and_property():
    backend = AmazeSynthesizer(max_cost=2, max_candidates=20)
    result = solve_source(
        """@minimize_size @example(f 0 = 1) def f(x:Int):{v:Int | v > 0} := ?body;
        @property(2) def law(x:Int):Bool := f x > 0;""",
        backend,
        budget=5,
    )
    assert next(iter(result.values())) == Literal(1, t_int)
    assert backend.pareto_front


@pytest.mark.parametrize("backend_name", ["enumerative", "random_search"])
def test_native_search_exposes_and_resets_archive(backend_name):
    from aeon.synthesis.modules.synthesizerfactory import make_synthesizer

    backend = make_synthesizer(backend_name)
    result = solve_source("@minimize_int(f) def f:{v:Int | v >= 0} := ?body;", backend, budget=0.3)
    assert next(iter(result.values())) in [term for _, term in backend.pareto_front]
    solve_source("def f:Int := ?body;", backend, budget=0.3)
    assert backend.pareto_front == []


@pytest.mark.parametrize("valid", [True, False])
def test_dp_reference_accepts_examples_and_checks_additional_properties(valid):
    source = (Path(__file__).parents[1] / "examples/synthesis/dp_gp/knapsack.ae").read_text()
    source = source.replace(
        "@dp_gp(reference, 4, 5)",
        '@example(optimized 0 0 = 0)\n@csv_data("0,0,0\\n1,0,1")\n@dp_gp(reference, 4, 5)',
    )
    comparison = ">=" if valid else "<"
    source += f"\n@property(2) def law(n:{{v:Int | v >= 0 && v <= 4}}):Bool := optimized n 0 {comparison} 0;"
    driver = parse(source)
    backend = DPSynthesizer(config=DPConfig(proposals=160))
    if valid:
        assert all(value is not None for value in solve(driver, backend, budget=30).values())
    else:
        with pytest.raises(SynthesisNotSuccessful, match="additional specifications"):
            solve(driver, backend, budget=30)


def test_dp_does_not_claim_to_optimize_a_single_reference_transform():
    source = (Path(__file__).parents[1] / "examples/synthesis/dp_gp/knapsack.ae").read_text()
    source = source.replace("@dp_gp(reference, 4, 5)", "@minimize_int(optimized 0 0)\n@dp_gp(reference, 4, 5)")
    with pytest.raises(UnsupportedSynthesisGoal, match="cannot optimize"):
        solve(parse(source), DPSynthesizer(), budget=30)


def test_regus_combines_control_objective_size_examples_and_properties():
    from aeon.synthesis.modules.regus import ReGuSSynthesizer
    from aeon.synthesis.modules.regus.search import Config
    from tests.regus_test import TOY, parse as parse_control, solve as solve_control

    source = TOY.replace("DESIRED", "0").replace(
        "@minimize_float(fitness controller)",
        "@minimize_float(fitness controller)\n@minimize_cputime(fitness controller)\n@minimize_size\n@example(ControlProgram.closed controller)",
    )
    source += "\n@property(1) def law(x:Bool):Bool := ControlProgram.closed controller;"
    backend = ReGuSSynthesizer(
        config=Config(max_nodes=2, max_loops=1, max_sketch_nodes=1, max_states=8, completion_batch=1)
    )
    solve_control(parse_control(source), backend, budget=10)
    assert backend.pareto_front
    assert all(len(scores) == 5 for scores, _ in backend.pareto_front)


def test_sygus_combines_refinement_examples_csv_properties_and_objectives():
    from aeon.synthesis.modules.sygus import SygusSynthesizer

    backend = SygusSynthesizer()
    result = solve_source(
        r"""
        @doc("Return zero.")
        @example(f 0 = 0)
        @csv_data("0,0\n1,0")
        @minimize_int(f 0)
        @maximize_int(f 1)
        @minimize_size
        def f(x:Int):{v:Int | v = 0} := ?body;
        @property(3) def law(x:Int):Bool := f x = 0;
        """,
        backend,
        budget=3,
    )
    assert next(iter(result.values())) == Literal(0, t_int)
    assert backend.pareto_front
    assert all(sorted(scores) == [0.0, 0.0, 0.0, 0.0, 0.0, 1.0] for scores, _ in backend.pareto_front)
