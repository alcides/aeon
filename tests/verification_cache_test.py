"""Reusable SMT work must remain specific to its data and logical assumptions."""

import pytest
import z3

from aeon.compilation.session import CompilationOptions, CompilationSession
from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralFloat, LiquidLiteralInt, LiquidVar
from aeon.core.types import AbstractionType, RefinedType, t_float, t_int, t_unit
from aeon.utils.name import Name
from aeon.verification import smt
from aeon.verification.state import VerificationState
from aeon.verification.vcs import (
    Conjunction,
    Implication,
    LiquidConstraint,
    ReflectedFunctionDeclaration,
    UninterpretedFunctionDeclaration,
)


def app(operator, *args):
    return LiquidApp(Name(operator, 0), list(args))


def test_literal_arrays_and_symbolic_reads_are_reused(monkeypatch):
    with CompilationSession().activate():
        table = smt._array_literal(3, 7, 11)
        assert smt._array_literal(3, 7, 11) is table
        index = z3.Int("index")
        read = smt._array_get(table, index)

        def unexpected_translation(*args):
            pytest.fail("an unchanged table read was rebuilt")

        monkeypatch.setattr(smt, "_array_get_uncached", unexpected_translation)
        assert smt._array_get(table, index) is read
        solver = z3.Solver()
        solver.add(index == 1, read != 7)
        assert solver.check() == z3.unsat


def test_array_cache_keeps_contents_indices_and_sorts_distinct():
    with CompilationSession().activate():
        for values in [(3, 7), (7, 3), (True, False), (3.5, 7.5), ("a", "b")]:
            table = smt._array_literal(*values)
            for index, expected in enumerate(values):
                assert z3.is_true(z3.simplify(smt._array_get(table, index) == expected))
            for index in [-1, len(values)]:
                # Out-of-bounds reads retain the sequence theory's semantics.
                assert z3.is_true(z3.simplify(smt._array_get(table, index) == table[index]))


def test_array_caches_are_bounded_and_session_local():
    first, second = CompilationSession(CompilationOptions(cache_limit=3)), CompilationSession()
    with first.activate():
        for value in range(10):
            table = smt._array_literal(value, value + 1)
            smt._array_get(table, z3.Int("index"))
        state = first.state(VerificationState)
        assert 0 < len(state.array_reads) <= 3
        assert 0 < len(state.array_literals) <= 3
        assert 0 < len(state.array_elements) <= 3
        smt.clear_smt_caches()
        assert not state.array_reads and not state.array_literals and not state.array_elements
    with second.activate():
        assert not second.state(VerificationState).array_reads


def test_changed_reflected_body_is_not_reused():
    with CompilationSession().activate():
        x, f = Name("x", 900), Name("f", 901)
        call = LiquidApp(f, [LiquidLiteralInt(4)])
        for offset in [1, 2, 1]:
            definitions = {str(f): ((x,), app("+", LiquidVar(x), LiquidLiteralInt(offset)))}
            result = smt.ple_unfold_fixpoint(call, definitions)
            assert result == app("+", LiquidLiteralInt(4), LiquidLiteralInt(offset))


def test_unchanged_clause_is_reused_when_another_definition_changes(monkeypatch):
    with CompilationSession().activate():
        calls = []
        original = smt.translate

        def translate(*args):
            calls.append(args)
            return original(*args)

        monkeypatch.setattr(smt, "translate", translate)

        def program(fresh_id, other):
            x = Name("x", fresh_id)
            shared = Implication(
                x,
                t_int,
                app(">", LiquidVar(x), LiquidLiteralInt(0)),
                LiquidConstraint(app(">=", LiquidVar(x), LiquidLiteralInt(0))),
            )
            return Conjunction(shared, LiquidConstraint(app("<", LiquidLiteralInt(0), LiquidLiteralInt(other))))

        assert smt.smt_valid(program(1000, 1))
        assert len(calls) == 2
        assert smt.smt_valid(program(1001, 2))
        assert len(calls) == 3


def test_changed_premise_is_not_reused():
    with CompilationSession().activate():
        x = Name("x", 1100)
        claim = LiquidConstraint(app(">=", LiquidVar(x), LiquidLiteralInt(0)))
        assert smt.smt_valid(Implication(x, t_int, app(">", LiquidVar(x), LiquidLiteralInt(0)), claim))
        assert not smt.smt_valid(Implication(x, t_int, app("<", LiquidVar(x), LiquidLiteralInt(0)), claim))


def test_changed_variable_sort_is_not_reused():
    with CompilationSession().activate():
        x, y = Name("x", 1200), Name("y", 1201)
        claim = LiquidConstraint(app("==", LiquidVar(x), LiquidVar(y)))
        for ty, expected in [(t_unit, True), (t_int, False)]:
            vc = Implication(x, ty, LiquidLiteralBool(True), Implication(y, ty, LiquidLiteralBool(True), claim))
            assert smt.smt_valid(vc) == expected


def test_changed_function_signature_is_not_reused():
    with CompilationSession().activate():
        f, x = Name("f", 1300), Name("x", 1301)
        claim = LiquidConstraint(app("==", LiquidApp(f, [LiquidLiteralInt(0)]), LiquidApp(f, [LiquidLiteralInt(1)])))
        for result, expected in [(t_unit, True), (t_int, False)]:
            vc = UninterpretedFunctionDeclaration(f, AbstractionType(x, t_int, result), claim)
            assert smt.smt_valid(vc) == expected


def test_changed_reflection_invalidates_clause_proof():
    with CompilationSession().activate():
        f, x = Name("f", 1400), Name("x", 1401)
        ty = AbstractionType(x, t_int, t_int)
        claim = LiquidConstraint(app("==", LiquidApp(f, [LiquidLiteralInt(0)]), LiquidLiteralInt(1)))
        for result, expected in [(1, True), (2, False)]:
            vc = ReflectedFunctionDeclaration(f, ty, (x,), LiquidLiteralInt(result), claim)
            assert smt.smt_valid(vc) == expected


def test_sort_of_variable_referenced_only_in_a_function_contract_is_not_reused():
    with CompilationSession().activate():
        f, x, y, result = Name("f", 1450), Name("x", 1451), Name("y", 1452), Name("result", 1453)
        ty = AbstractionType(x, t_int, RefinedType(result, t_float, app("==", LiquidVar(result), LiquidVar(y))))
        claim = LiquidConstraint(app("!=", LiquidApp(f, [LiquidLiteralInt(0)]), LiquidLiteralFloat(0.5)))
        for sort, expected in [(t_int, True), (t_float, False)]:
            vc = Implication(y, sort, LiquidLiteralBool(True), UninterpretedFunctionDeclaration(f, ty, claim))
            assert smt.smt_valid(vc) == expected


def test_only_successful_proofs_are_retained(monkeypatch):
    with CompilationSession().activate() as session:
        x = Name("x", 1500)
        valid = Implication(
            x,
            t_int,
            app(">", LiquidVar(x), LiquidLiteralInt(0)),
            LiquidConstraint(app(">=", LiquidVar(x), LiquidLiteralInt(0))),
        )
        with monkeypatch.context() as patch:
            patch.setattr(z3.Solver, "check", lambda *args: z3.unknown)
            assert not smt.smt_valid(valid)
        state = session.state(VerificationState)
        assert not state.proved_clauses
        smt.clear_smt_caches()
        invalid = LiquidConstraint(app("<", LiquidLiteralInt(1), LiquidLiteralInt(0)))
        assert not smt.smt_valid(invalid)
        assert not state.proved_clauses
        assert smt.smt_valid(valid)
        assert state.proved_clauses
        smt.clear_smt_caches()
        assert not state.proved_clauses
