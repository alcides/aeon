"""Incremental pruning reuses proofs without mixing branches or scopes."""

import pytest
import z3

from aeon.compilation.session import CompilationOptions, CompilationSession
from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
from aeon.core.parser import parse_type
from aeon.core.types import t_int
from aeon.synthesis.modules.tdsyn.constraints import existential_formula, feasible
from aeon.synthesis.modules.tdsyn.incremental import IncrementalState, solver_query
from aeon.synthesis.modules.tdsyn.smt_solve import solve_literals
from aeon.synthesis.modules.tdsyn.worklist import fresh_hole
from aeon.typechecking.context import TypingContext, VariableBinder
from aeon.utils.name import Name


def eq(name, value):
    return LiquidApp(Name("==", 0), [LiquidVar(name), LiquidLiteralInt(value)])


@pytest.mark.parametrize("limit", [8, 1024])
def test_incremental_siblings_match_fresh_queries(limit):
    with CompilationSession(CompilationOptions(cache_limit=limit)).activate():
        ctx = TypingContext()
        x, y = Name("x", 101), Name("y", 102)
        bindings = {x: t_int, y: t_int}
        related = LiquidApp(Name("==", 0), [LiquidVar(x), LiquidVar(y)])
        for a, b in [(0, 0), (0, 1), (1, 1), (1, 0), (0, 0)]:
            predicates = [eq(x, a), related, eq(y, b)]
            fresh = z3.Solver()
            fresh.add(existential_formula(ctx, bindings, predicates))
            assert feasible(ctx, bindings, predicates) == (fresh.check() == z3.sat) == (a == b)


def test_only_new_atoms_are_translated(monkeypatch):
    import aeon.synthesis.modules.tdsyn.constraints as constraints

    with CompilationSession().activate():
        ctx = TypingContext()
        x, y = Name("x", 201), Name("y", 202)
        original = constraints.existential_formula
        calls = []

        def translate(*args):
            calls.append(args)
            return original(*args)

        monkeypatch.setattr(constraints, "existential_formula", translate)
        assert feasible(ctx, {x: t_int}, [eq(x, 1)])
        assert feasible(ctx, {x: t_int, y: t_int}, [eq(x, 1), eq(y, 2)])
        assert len(calls) == 2
        assert feasible(ctx, {x: t_int}, [eq(x, 1)])
        assert len(calls) == 2


def test_model_blockers_do_not_leak_into_another_enumeration():
    with CompilationSession().activate():
        _, hole = fresh_hole(parse_type("{v:Int | v >= 0 && v <= 1}"), TypingContext())
        for _ in range(3):
            values = {model[hole.name].value for model in solve_literals([hole])}
            assert values == {0, 1}


def test_weaker_branch_does_not_inherit_a_previous_refinement():
    with CompilationSession().activate():
        ctx, x = TypingContext(), Name("x", 301)
        assert not feasible(ctx, {x: parse_type("{v:Int | v == 0}")}, [eq(x, 1)])
        assert feasible(ctx, {x: t_int}, [eq(x, 1)])


def test_mutated_context_invalidates_incremental_state():
    with CompilationSession().activate():
        ctx, x = TypingContext(), Name("x", 401)
        assert feasible(ctx, {x: t_int}, [eq(x, 1)])
        ctx.entries.append(VariableBinder(Name("impossible", 402), parse_type("{v:Int | false}")))
        assert not feasible(ctx, {x: t_int}, [eq(x, 1)])


def test_unsupported_atom_does_not_pollute_next_branch():
    with CompilationSession().activate():
        ctx, x = TypingContext(), Name("x", 501)
        unsupported = LiquidApp(Name("missing", 502), [LiquidVar(x)])
        assert feasible(ctx, {x: t_int}, [eq(x, 0), unsupported])
        assert feasible(ctx, {x: t_int}, [eq(x, 1)])


def test_shadowed_witness_uses_one_consistent_alpha_renaming():
    with CompilationSession().activate():
        x = Name("x", 601)
        ctx = TypingContext().with_var(x, t_int)
        assert not feasible(ctx, {x: t_int}, [eq(x, 0), eq(x, 1)])


def test_session_and_smt_reset_discard_incremental_state():
    from aeon.verification.smt import clear_smt_caches

    first, second = CompilationSession(), CompilationSession()
    ctx, x = TypingContext(), Name("x", 701)
    with first.activate():
        assert feasible(ctx, {x: t_int}, [eq(x, 1)])
        previous = first.state(IncrementalState).contexts[id(ctx)]
        clear_smt_caches()
        assert feasible(ctx, {x: t_int}, [eq(x, 2)])
        assert first.state(IncrementalState).contexts[id(ctx)] is not previous
    with second.activate():
        assert not second.state(IncrementalState).contexts
        assert feasible(ctx, {x: t_int}, [eq(x, 3)])


def test_query_scope_is_restored_after_exception():
    with CompilationSession().activate():
        ctx, x = TypingContext(), Name("x", 801)
        with pytest.raises(RuntimeError):
            with solver_query(ctx, {x: t_int}, [eq(x, 1)]) as (solver, assumptions):
                solver.add(z3.BoolVal(False))
                raise RuntimeError("abort model enumeration")
        assert feasible(ctx, {x: t_int}, [eq(x, 1)])


def test_nested_queries_do_not_share_model_blockers_or_drop_cached_assertions():
    with CompilationSession().activate():
        ctx, x = TypingContext(), Name("x", 901)
        with solver_query(ctx, {x: t_int}, [eq(x, 1)]) as (solver, assumptions):
            solver.add(z3.BoolVal(False))
            assert feasible(ctx, {x: t_int}, [eq(x, 2)])
            assert solver.check(*assumptions) == z3.unsat
        assert not feasible(ctx, {x: t_int}, [eq(x, 2), eq(x, 3)])
