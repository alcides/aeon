"""Tests for the SyGuS synthesis backend (issue #49).

Covers the three phases: translating an Aeon-core hole to a SyGuS problem,
solving it with the cvc5 SyGuS Python API, and validating that the
reverse-translated Aeon-core term type-checks against the hole's refined type.
"""

from __future__ import annotations

import pytest

from aeon.backend.evaluator import eval as aeon_eval
from aeon.core.substitutions import substitution
from aeon.core.terms import Var
from aeon.core.types import top
from aeon.logger.logger import setup_logger
from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.identification import get_holes_info, incomplete_functions_and_holes
from aeon.synthesis.modules.sygus import SygusSynthesizer
from aeon.synthesis.modules.sygus.translation import build_sygus_problem, problem_to_sl
from aeon.utils.name import Name

from tests.driver import check_and_return_core

setup_logger()

cvc5 = pytest.importorskip("cvc5")


def _synthesize(source: str, budget: float = 5.0):
    core, ctx, ectx, md = check_and_return_core(source)
    targets = incomplete_functions_and_holes(ctx, core)
    mapping = synthesize_holes(ctx, ectx, core, targets, md, SygusSynthesizer(), budget=budget)
    return core, ectx, mapping


def test_constant_int_synthesis():
    """``{x:Int | x == 35}`` should synthesize the constant 35."""
    _, _, mapping = _synthesize("def n : {x:Int | x = 35} := ?hole;")
    (term,) = mapping.values()
    assert term is not None
    assert eval_int_program("def n : {x:Int | x = 35} := ?hole;", term) == 35


def test_linear_equation_synthesis():
    """``{n:Int | n + 4 == 7}`` should synthesize 3."""
    src = "def x_solution : {n:Int | n + 4 = 7} := ?hole"
    _, _, mapping = _synthesize(src)
    (term,) = mapping.values()
    assert eval_int_program(src, term) == 3


def test_quadratic_synthesis():
    """``{n:Int | n * n == 4}`` should synthesize a value whose square is 4."""
    src = "def x_solution : {n:Int | n * n = 4} := ?hole"
    _, _, mapping = _synthesize(src)
    (term,) = mapping.values()
    val = eval_int_program(src, term)
    assert val * val == 4


def test_function_of_input_synthesis():
    """A hole that must depend on an input: ``z == x + 1`` -> ``x + 1``."""
    src = "def f(x:{k:Int | k > 0}) : {z:Int | z = x + 1} := ?h"
    _, _, mapping = _synthesize(src)
    (term,) = mapping.values()
    assert term is not None  # validated inside synthesize_holes


def test_precondition_constant_synthesis():
    """``x>0 => z<0`` is satisfiable by a constant; backend should find one."""
    src = "def test(x:{k:Int | k > 0}) : {z:Int | z < 0} := ?r"
    _, _, mapping = _synthesize(src)
    (term,) = mapping.values()
    assert term is not None


def test_graceful_failure_non_smt_type():
    """A hole of a non-SMT (inductive) type is outside the subset."""
    src = "inductive P\n| mk (v:Int | 0 < v && v < 10 ) : P\n\ndef func : P := ?hole"
    with pytest.raises(SynthesisNotSuccessful):
        _synthesize(src)


def test_translation_emits_sygus_if():
    """The translation phase should produce well-formed SyGuS-IF text."""
    src = "def f(x:{k:Int | k > 0}) : {z:Int | z = x + 1} := ?h"
    core, ctx, _, _ = check_and_return_core(src)
    targets = incomplete_functions_and_holes(ctx, core)
    holes = get_holes_info(ctx, core, top, targets, refined_types=True)
    (fn, hs) = targets[0]
    ty, tyctx = holes[hs[0]]
    problem = build_sygus_problem(tyctx, ty, fun_name=fn.name)
    assert problem is not None
    text = problem_to_sl(problem)
    assert "(synth-fun f" in text
    assert "(check-synth)" in text
    assert "(=>" in text  # precondition implication
    assert "(declare-var" in text


def test_translation_rejects_non_refined_type():
    """A plain (unrefined) type has no spec and is not handled here."""
    src = "def n : Int := ?hole"
    core, ctx, _, _ = check_and_return_core(src)
    targets = incomplete_functions_and_holes(ctx, core)
    holes = get_holes_info(ctx, core, top, targets, refined_types=True)
    (fn, hs) = targets[0]
    ty, tyctx = holes[hs[0]]
    assert build_sygus_problem(tyctx, ty, fun_name=fn.name) is None


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------


def eval_int_program(source: str, term) -> int:
    """Substitute ``term`` for the hole and evaluate the defined value."""
    core, ctx, ectx, _ = check_and_return_core(source)
    targets = incomplete_functions_and_holes(ctx, core)
    (_, hs) = targets[0]
    hole_name = hs[0]
    # Replace the hole, then point ``main`` at the synthesised definition.
    filled = substitution(core, term, hole_name)
    def_name = targets[0][0]
    program = substitution(filled, Var(def_name), Name("main", 0))
    return aeon_eval(program, ectx)
