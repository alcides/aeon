"""Unchosen arguments are existential witnesses; completed terms are verified."""

import pytest
import z3

from aeon.core.liquid import LiquidLiteralBool
from aeon.core.parser import parse_type
from aeon.core.terms import Application, Literal, Var
from aeon.core.types import t_int
from aeon.synthesis.modules.tdsyn.actions import backward_app_candidates, forward_candidates
from aeon.synthesis.modules.tdsyn.constraints import candidate_feasible, feasible
from aeon.synthesis.modules.tdsyn.helpers import clear_tdsyn_caches
from aeon.synthesis.modules.tdsyn.smt_solve import solve_literals
from aeon.synthesis.modules.tdsyn.worklist import PartialAST, expand_at_hole, fresh_hole
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


@pytest.fixture(autouse=True)
def clear_caches():
    clear_tdsyn_caches()


def application_problem(signature, goal):
    ctx = TypingContext().with_var(Name("f"), parse_type(signature))
    term, hole = fresh_hole(parse_type(goal), ctx)
    return PartialAST(term, [hole], 0), backward_app_candidates(hole, lambda _: False)


@pytest.mark.parametrize("domain,expected", [("Int", True), ("{v:Int | v > 10}", False)])
def test_dependent_application_asks_for_an_argument_witness(domain, expected):
    _, candidates = application_problem(f"(x:{domain}) -> {{v:Int | v == x + 1}}", "{v:Int | v == 10}")
    assert bool(candidates) is expected
    if expected:
        _, children = candidates[0]
        solutions = solve_literals(children)
        assert solutions and all(solution[children[0].name] == Literal(9, t_int) for solution in solutions)


def test_dependent_arguments_share_constraints_and_preserve_other_branches():
    partial, [(term, children)] = application_problem(
        "(x:Int) -> (y:{v:Int | v == x + 1}) -> {v:Int | v == x + y}", "{v:Int | v == 21}"
    )
    branch = expand_at_hole(partial, partial.holes[0], term, children, 1)
    x, y = branch.holes
    assert candidate_feasible(x, Literal(10, t_int), [])
    assert not candidate_feasible(x, Literal(9, t_int), [])
    chosen = expand_at_hole(branch, x, Literal(10, t_int), [], 1)
    solutions = solve_literals(chosen.holes)
    assert solutions and all(solution[y.name] == Literal(11, t_int) for solution in solutions)
    # Branch updates are persistent: the original still permits the same pair.
    assert candidate_feasible(x, Literal(10, t_int), [])
    assert y.constraints != chosen.holes[0].constraints


def test_forward_application_substitutes_supplied_argument_in_dependent_types():
    n = Name("n")
    ctx = (
        TypingContext()
        .with_var(n, parse_type("{v:Int | v == 8}"))
        .with_var(Name("f"), parse_type("(x:Int) -> (y:{v:Int | v > x}) -> {v:Int | v == x + y}"))
    )
    _, hole = fresh_hole(parse_type("{v:Int | v == 20}"), ctx)
    [(term, children)] = forward_candidates(hole, lambda _: False)
    assert isinstance(term, Application) and term.fun == Application(Var(Name("f")), Var(n))
    solutions = solve_literals(children)
    assert solutions and all(solution[children[0].name] == Literal(12, t_int) for solution in solutions)


def test_unknown_feasibility_keeps_candidate_for_final_validation(monkeypatch):
    monkeypatch.setattr(z3.Solver, "check", lambda *_: z3.unknown)
    assert feasible(TypingContext(), {}, [LiquidLiteralBool(False)])


def test_literal_completion_does_not_drop_untranslatable_refinements():
    _, hole = fresh_hole(parse_type("{v:Int | missing v}"), TypingContext())
    assert solve_literals([hole]) == []


def test_stochastic_expansion_defers_pruning_but_keeps_argument_contracts():
    from aeon.synthesis.modules.native_search import expansions_for_hole

    partial, _ = application_problem("(x:{v:Int | v > 10}) -> {v:Int | v == x + 1}", "{v:Int | v == 10}")
    hole = partial.holes[0]
    proposals = expansions_for_hole(partial, hole, lambda _: False, prune=False)
    applications = [p for p in proposals if isinstance(p.term, Application)]
    assert applications
    assert all(not solve_literals(p.holes) for p in applications)
    # Deferring a random walk's pruning must not change subsequent TDSyn search.
    assert not backward_app_candidates(hole, lambda _: False)
