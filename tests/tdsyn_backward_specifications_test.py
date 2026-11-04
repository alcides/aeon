"""Backward search shares TDSyn's validation, fitness and Pareto semantics."""

import pytest

from aeon.core.terms import Literal
from aeon.core.types import t_int
from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.identification import get_holes
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from tests.synthesis_specifications_test import solve


def test_backward_search_finishes_constructor_argument_subgoals():
    result = solve(
        "inductive Box | box (x:Int) : Box\ndef f:Box := ?body;",
        make_synthesizer("tdsyn_backward"),
        budget=2,
    )
    assert result and all(candidate is not None and not get_holes(candidate) for candidate in result.values())


def test_backward_search_reports_failure_instead_of_returning_partial_term():
    with pytest.raises(SynthesisNotSuccessful):
        solve("type Empty; def f:Empty := ?body;", make_synthesizer("tdsyn_backward"), budget=0.2)


@pytest.mark.parametrize("direction,expected", [("minimize", 0), ("maximize", 1)])
def test_backward_search_optimizes_beyond_first_valid_candidate(direction, expected):
    backend = make_synthesizer("tdsyn_backward")
    result = solve(
        f"@{direction}_int(f 0) def f(x:Int):{{v:Int | v >= 0 && v <= 1}} := ?body;",
        backend,
        budget=0.5,
    )
    assert list(result.values()) == [Literal(expected, t_int)]
    assert [scores for scores, _ in backend.pareto_front] == [[float(expected)]]


def test_backward_search_preserves_conflicting_objective_tradeoffs():
    backend = make_synthesizer("tdsyn_backward")
    result = solve(
        """@minimize_int(f 0) @maximize_int(f 0)
        def f(x:Int):{v:Int | v >= 0 && v <= 1} := ?body;""",
        backend,
        budget=0.5,
    )
    assert {tuple(scores) for scores, _ in backend.pareto_front} == {(0.0, 0.0), (1.0, 1.0)}
    assert next(iter(result.values())) in [term for _, term in backend.pareto_front]


def test_backward_search_keeps_tdsyn_soft_example_semantics():
    backend = make_synthesizer("tdsyn_backward")
    solve(
        """@example(f 0 = 0) @example(f 0 = 1)
        def f(x:Int):{v:Int | v >= 0 && v <= 1} := ?body;""",
        backend,
        budget=0.5,
    )
    assert {tuple(scores) for scores, _ in backend.pareto_front} == {(0.0, 1.0), (1.0, 0.0)}


@pytest.mark.parametrize("file", [False, True])
def test_backward_search_combines_both_csv_forms_with_properties_and_size(file, tmp_path):
    data = tmp_path / "examples.csv"
    data.write_text("0,1\n2,1\n")
    decorator = f'@csv_file("{data}")' if file else r'@csv_data("0,1\n2,1")'
    backend = make_synthesizer("tdsyn_backward")
    result = solve(
        f"""{decorator} @example(f 0 = 1) @minimize_size
        def f(x:Int):{{v:Int | v = 1}} := ?body;
        @property(3) def law(x:Int):Bool := f x = 1;""",
        backend,
        budget=0.5,
    )
    assert list(result.values()) == [Literal(1, t_int)]
    assert [scores for scores, _ in backend.pareto_front] == [[0.0, 0.0, 1.0, 0.0]]
