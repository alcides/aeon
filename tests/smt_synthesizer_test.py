"""Tests for the SMT-guided synthesis backend (``-s smt``, ``SMTSynthesizer``).

The backend builds an expression tree top-down, encodes the refinement on an
SMT base type (Int/Bool/Float) as z3 constraints, solves them, and substitutes
the resulting literal. These cover that refinement-solving path. (The
verification-layer z3 tests in ``smt_test``/``smt_sets_test`` exercise a
different component and do not touch this synthesizer.)
"""

from __future__ import annotations

from aeon.core.terms import Literal
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.modules.smt_synthesizer import SMTSynthesizer
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer

from tests.driver import check_and_return_core


def _solve(code: str, budget: float = 10.0):
    term, ctx, ectx, metadata = check_and_return_core(code)
    targets = incomplete_functions_and_holes(ctx, term)
    holes = synthesize_holes(ctx, ectx, term, targets, metadata, SMTSynthesizer(), budget=budget)
    return holes[next(iter(holes))]


def test_factory_registers_smt():
    assert isinstance(make_synthesizer("smt"), SMTSynthesizer)


def test_solves_linear_refinement():
    t = _solve("def n : {v:Int | v + 4 = 7} := ?hole;")
    assert isinstance(t, Literal) and t.value == 3


def test_solves_conjoined_refinement():
    t = _solve("def m : {v:Int | v * 2 = 10 && v - 1 = 4} := ?hole;")
    assert isinstance(t, Literal) and t.value == 5


def test_solves_constant_int_refinement():
    t = _solve("def k : {x:Int | x = 35} := ?hole;")
    assert isinstance(t, Literal) and t.value == 35


def test_solves_bool_refinement():
    t = _solve("def b : {z:Bool | z = true} := ?hole;")
    assert isinstance(t, Literal) and t.value is True


def test_solves_float_refinement():
    t = _solve("def p : {x:Float | x = 2.5} := ?hole;")
    assert isinstance(t, Literal) and t.value == 2.5
