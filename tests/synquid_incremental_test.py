"""Incremental validity queries preserve branch isolation and three-valued results."""

from time import monotonic

import pytest
import z3

from aeon.compilation.session import CompilationOptions, CompilationSession
from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt, LiquidVar
from aeon.core.types import AbstractionType, t_int, t_unit
from aeon.synthesis.modules.synquid.constraints import ConstraintState
from aeon.synthesis.modules.synquid.solver import SMTQuery, Status
from aeon.utils.ctx_helpers import built_std_context
from aeon.utils.name import Name
from aeon.verification.smt import clear_smt_caches, flatten, translate
from aeon.verification.vcs import Conjunction, Implication, LiquidConstraint, ReflectedFunctionDeclaration


def app(op, *args):
    return LiquidApp(Name(op, 0), list(args))


def obligation(premise, conclusion, ident=101):
    x = Name("x", ident)
    return Implication(
        x,
        t_int,
        app("==", LiquidVar(x), LiquidLiteralInt(premise)),
        LiquidConstraint(app("==", LiquidVar(x), LiquidLiteralInt(conclusion))),
    )


@pytest.mark.parametrize("limit", [1, 3, 1024])
def test_queries_match_fresh_solver_without_branch_leaks(limit):
    with CompilationSession(CompilationOptions(cache_limit=limit)).activate():
        query = SMTQuery()
        for a, b in [(1, 1), (1, 2), (2, 1), (2, 2), (1, 1)]:
            vc = obligation(a, b)
            solver = z3.Solver()
            solver.add(z3.Or(*[translate(c) for c in flatten(vc)]))
            expected = Status.VALID if solver.check() == z3.unsat else Status.INVALID
            assert query.valid(vc) == expected
            assert len(query.state.queries) <= limit
            assert query.state.clause_count <= limit


def test_search_forks_reuse_solver_and_translation(monkeypatch):
    import aeon.synthesis.modules.synquid.solver as smt

    with CompilationSession().activate():
        state = ConstraintState(built_std_context())
        calls = []
        original = smt.translate

        def counted(clause):
            calls.append(clause)
            return original(clause)

        monkeypatch.setattr(smt, "translate", counted)
        assert state.query.valid(obligation(1, 1)) == Status.VALID
        solver = state.solver_state.solver
        child = state.fork()
        assert child.solver_state is state.solver_state
        assert child.query.valid(obligation(1, 1, ident=202)) == Status.VALID
        assert child.solver_state.solver is solver
        assert len(calls) == 1
        assert child.query.valid(obligation(1, 2)) == Status.INVALID
        assert state.query.valid(obligation(1, 1)) == Status.VALID
        assert len(calls) == 2


def test_changed_reflected_definition_is_not_reused():
    with CompilationSession().activate():
        f, x = Name("f", 301), Name("x", 302)
        query = SMTQuery()
        for value, expected in [(1, Status.VALID), (2, Status.INVALID), (1, Status.VALID)]:
            vc = ReflectedFunctionDeclaration(
                f,
                AbstractionType(x, t_int, t_int),
                (x,),
                LiquidLiteralInt(value),
                LiquidConstraint(app("==", LiquidApp(f, [LiquidLiteralInt(0)]), LiquidLiteralInt(1))),
            )
            assert query.valid(vc) == expected


def test_changed_sort_is_not_reused():
    with CompilationSession().activate():
        query = SMTQuery()
        x, y = Name("x", 401), Name("y", 402)
        for sort, expected in [(t_unit, Status.VALID), (t_int, Status.INVALID)]:
            vc = Implication(
                x,
                sort,
                LiquidLiteralBool(True),
                Implication(y, sort, LiquidLiteralBool(True), LiquidConstraint(app("==", LiquidVar(x), LiquidVar(y)))),
            )
            assert query.valid(vc) == expected


def test_unknown_and_expired_queries_can_be_retried(monkeypatch):
    with CompilationSession().activate():
        query = SMTQuery(timeout_ms=100)
        vc = obligation(1, 1)
        with monkeypatch.context() as patch:
            patch.setattr(z3.Solver, "check", lambda *_: z3.unknown)
            assert query.valid(vc) == Status.UNKNOWN
        assert query.valid(vc) == Status.VALID
        query.deadline = monotonic() - 1
        assert query.valid(vc) == Status.UNKNOWN
        query.deadline = float("inf")
        assert query.valid(vc) == Status.VALID


def test_unsupported_clause_does_not_poison_following_queries(monkeypatch):
    import aeon.synthesis.modules.synquid.solver as smt

    with CompilationSession().activate():
        query = SMTQuery()
        undefined = LiquidConstraint(app("==", app("/", LiquidLiteralInt(1), LiquidLiteralInt(0)), LiquidLiteralInt(0)))
        original = smt.translate

        def unsupported(clause):
            if clause.conclusion == undefined.expr:
                raise NotImplementedError("unsupported theory")
            return original(clause)

        monkeypatch.setattr(smt, "translate", unsupported)
        assert query.valid(Conjunction(obligation(1, 1), undefined)) == Status.UNSUPPORTED
        assert query.valid(obligation(1, 2)) == Status.INVALID
        assert query.valid(obligation(1, 1)) == Status.VALID


def test_session_and_datatype_resets_discard_queries():
    query = SMTQuery()
    vc = obligation(1, 1)
    with CompilationSession().activate():
        assert query.valid(vc) == Status.VALID
        original = next(iter(query.state.queries.values()))
        clear_smt_caches()
        assert query.valid(vc) == Status.VALID
        after_reset = next(iter(query.state.queries.values()))
        assert after_reset is not original
    with CompilationSession().activate():
        assert query.valid(vc) == Status.VALID
        assert next(iter(query.state.queries.values())) is not after_reset


def test_oversized_query_does_not_leave_unbounded_solver_assertions():
    with CompilationSession(CompilationOptions(cache_limit=1)).activate():
        query = SMTQuery()
        assert query.valid(obligation(1, 1)) == Status.VALID
        solver = query.state.solver
        vc = Conjunction(obligation(2, 2), obligation(3, 3))
        assert query.valid(vc) == Status.VALID
        assert query.state.solver is solver
        assert len(solver.assertions()) == 1
        assert query.valid(obligation(1, 2)) == Status.INVALID
