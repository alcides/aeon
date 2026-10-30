"""Weakest satisfiable guards, alternative strengthenings and SMT edge cases."""

import z3

from aeon.core.liquid import LiquidLiteralBool, LiquidLiteralInt, LiquidVar
from tests.synquid_round_trip_test import parse_type
from aeon.core.terms import Annotation, If, Literal, Var
from aeon.core.types import t_bool, t_int
from aeon.synthesis.modules.synquid.abduction import abduce
from aeon.synthesis.modules.synquid.constraints import ConstraintState
from aeon.synthesis.modules.synquid.engine import synthes_memory
from aeon.synthesis.modules.synquid.solver import SMTQuery, Status, minimal_subsets
from aeon.typechecking.typeinfer import check_type
from aeon.utils.ctx_helpers import built_std_context
from aeon.verification.vcs import LiquidConstraint
from tests.synquid_round_trip_test import liq, name


def maximum():
    ctx = built_std_context().with_var(name("x"), t_int).with_var(name("y"), t_int)
    goal = parse_type("{v:Int | ((v >= x) && (v >= y)) && ((v == x) || (v == y))}")
    return ctx, goal


def test_maximum_abduces_weakest_guard_and_verifies_complete_conditional():
    ctx, goal = maximum()
    state = ConstraintState(ctx)
    result = abduce(state, Var(name("x")), goal)
    assert result.status == Status.VALID
    assert len(result.guards) == 1
    guard, term = result.guards[0]
    expected = liq(">=", LiquidVar(name("x")), LiquidVar(name("y")))
    assert state.assume(guard).query.valid(state.assume(guard).lift(LiquidConstraint(expected))) == Status.VALID
    assert state.assume(expected).query.valid(state.assume(expected).lift(LiquidConstraint(guard))) == Status.VALID
    assert check_type(ctx, Annotation(If(term, Var(name("x")), Var(name("y"))), goal), goal)
    assert state.stats.abduction_branches == 1
    assert state.stats.fallback_guards == 0
    assert state.stats.unsat_cores > 0


def test_branch_first_engine_builds_max_and_else_under_negation():
    ctx, goal = maximum()
    mem = {}
    terms = synthes_memory(ctx, 1, goal, lambda n: n.name not in ("x", "y"), mem)
    found = next(t for t in terms if check_type(ctx, t, goal))
    assert isinstance(found, Annotation) and isinstance(found.expr, If)
    assert mem["synquid_stats"].abduced_guards == 1
    assert mem["synquid_stats"].fallback_guards == 0


def test_insufficient_qualifiers_and_inconsistent_context_do_not_accept():
    ctx, goal = maximum()
    assert abduce(ConstraintState(ctx), Var(name("x")), goal, qualifiers=frozenset()).status == Status.EXHAUSTED
    result = abduce(ConstraintState(ctx).assume(LiquidLiteralBool(False)), Var(name("x")), goal)
    assert not result.guards


def test_mus_enumeration_retains_incomparable_minimal_sets():
    # (q0 && q1) || q2: neither minimal strengthening may be discarded.
    def valid(s):
        return Status.VALID if {0, 1} <= s or 2 in s else Status.INVALID

    subsets, status = minimal_subsets(3, valid)
    assert status == Status.VALID
    assert set(subsets) == {frozenset({0, 1}), frozenset({2})}


def test_unknown_is_not_a_counterexample(monkeypatch):
    monkeypatch.setattr(z3.Solver, "check", lambda *_: z3.unknown)
    assert SMTQuery().valid(LiquidConstraint(LiquidLiteralBool(False))) == Status.UNKNOWN
    subsets, status = minimal_subsets(1, lambda _: Status.UNKNOWN)
    assert status == Status.UNKNOWN
    assert subsets == []


def test_unsupported_sort_is_explicit():
    bad = LiquidConstraint(liq("<", LiquidLiteralBool(True), LiquidLiteralInt(1)))
    assert SMTQuery().valid(bad) == Status.UNSUPPORTED


def test_boolean_variables_are_executable_guards():
    from aeon.core.types import RefinedType

    ctx = built_std_context().with_var(name("flag"), t_bool)
    goal = RefinedType(name("v"), t_int, LiquidVar(name("flag")))
    result = abduce(ConstraintState(ctx), Literal(0, t_int), goal, qualifiers=frozenset({LiquidVar(name("flag"))}))
    assert result.status == Status.VALID
    assert result.guards == [(LiquidVar(name("flag")), Var(name("flag")))]


def test_semantic_minimization_compares_whole_conjunctions():
    x, y = LiquidVar(name("x")), LiquidVar(name("y"))
    zero = LiquidLiteralInt(0)
    weak = liq(">=", liq("+", x, y), zero)
    ctx = built_std_context().with_var(name("x"), t_int).with_var(name("y"), t_int)
    state = ConstraintState(ctx)
    predicate = state.fresh_predicate(ctx, frozenset({liq(">=", x, zero), liq(">=", y, zero), weak}))
    state.add(state.assume(predicate).lift(LiquidConstraint(weak)), lifted=True)
    assert state.solve() == Status.VALID
    # {x >= 0, y >= 0} is syntactically minimal but semantically stronger.
    assert len(state.assignments) == 1


def test_branch_construction_abduces_argument_preconditions():
    from aeon.synthesis.modules.synquid.abduction import branch_environment

    ctx = built_std_context().with_var(name("x"), t_int)
    ctx = ctx.with_var(name("positive"), parse_type("(n:{v:Int | v > 0}) -> {v:Int | v == n}"))
    goal = parse_type("{v:Int | ((v >= x) && (v >= 0)) && ((v == x) || (v == 0))}")
    state = branch_environment(ConstraintState(ctx), goal)
    proposals = list(
        synthes_memory(ctx, 1, goal, lambda n: n.name not in ("x", "positive"), {}, state, conditionals=False)
    )
    assert any("positive" in str(t) and "x" in str(t) for t in proposals)
    branch = next(t for t in proposals if "positive" in str(t) and "x" in str(t))
    assert not check_type(ctx, branch, goal)
    result = abduce(ConstraintState(ctx), branch, goal)
    assert result.guards


def test_incremental_predicate_alternatives_and_forks_are_isolated():
    from aeon.verification.horn import apply_liquid

    x = LiquidVar(name("x"))
    positive, negative = liq(">", x, LiquidLiteralInt(0)), liq("<", x, LiquidLiteralInt(0))
    ctx = built_std_context().with_var(name("x"), t_int)
    state = ConstraintState(ctx)
    predicate = state.fresh_predicate(ctx, frozenset({positive, negative}))
    # Horn antecedents are represented as implication assumptions in VCs.
    state.add(state.assume(predicate).lift(LiquidConstraint(liq("!=", x, LiquidLiteralInt(0)))), lifted=True)
    assert state.solve() == Status.VALID
    assert len(state.assignments) == 2
    for condition in (positive, negative):
        child = state.fork()
        child.add(child.assume(predicate).lift(LiquidConstraint(condition)), lifted=True)
        assert child.solve() == Status.VALID
        assert len(child.assignments) == 1
        guard = apply_liquid(child.assignments[0], predicate)
        assert child.assume(guard).query.valid(child.assume(guard).lift(LiquidConstraint(condition))) == Status.VALID
    assert len(state.assignments) == 2


def test_minimal_guards_are_semantically_weakest_in_finite_vocabulary():
    from itertools import combinations
    from aeon.verification.horn import merge_assignments
    from aeon.typechecking.typeinfer import check

    ctx, goal = maximum()
    x, y = LiquidVar(name("x")), LiquidVar(name("y"))
    vocabulary = [liq(">=", x, y), liq(">", x, y), liq("!=", x, y)]
    result = abduce(ConstraintState(ctx), Var(name("x")), goal, qualifiers=frozenset(vocabulary))
    assert result.status == Status.VALID and len(result.guards) == 1
    guard = result.guards[0][0]
    for size in range(len(vocabulary) + 1):
        for chosen in combinations(vocabulary, size):
            candidate = merge_assignments(list(chosen))
            candidate_state = ConstraintState(ctx).assume(candidate)
            if candidate_state.inhabited() != Status.INVALID:
                continue
            valid = candidate_state.query.valid(candidate_state.lift(check(ctx, Var(name("x")), goal)))
            if valid == Status.VALID:
                assert candidate_state.query.valid(candidate_state.lift(LiquidConstraint(guard))) == Status.VALID


def test_mus_budget_exhaustion_is_unknown_and_preserves_state():
    ctx, goal = maximum()
    state = ConstraintState(ctx, max_checks=0)
    result = abduce(state, Var(name("x")), goal)
    assert result.status == Status.UNKNOWN
    assert result.guards == []
    assert not state.constraints and state.assignments == [{}]


def test_mus_requires_the_negated_head_not_just_inconsistent_predicates():
    x = LiquidVar(name("x"))
    ctx = built_std_context().with_var(name("x"), t_int)
    state = ConstraintState(ctx)
    positive = state.fresh_predicate(ctx, frozenset({liq(">", x, LiquidLiteralInt(0))}))
    negative = state.fresh_predicate(ctx, frozenset({liq("<", x, LiquidLiteralInt(0))}))
    state.add(state.assume(positive).assume(negative).lift(LiquidConstraint(LiquidLiteralBool(False))), lifted=True)
    # Both valuations can be individually nonempty, yet their conjunction
    # cannot be used to prove an arbitrary Horn head by contradiction.
    assert state.solve() == Status.EXHAUSTED
