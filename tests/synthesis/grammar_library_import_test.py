"""Regression test: building the synthesis grammar for a hole whose context
contains library functions with dependent or abstract refinements must not
crash.

Importing a library (e.g. ``Math``, ``Array``) into a file with a hole brings
shapes the grammar generator could not represent into the hole's typing context:

* ``Math.clamp`` -- ``hi: {v:Int | v >= lo}``, a refinement mentioning a
  *sibling* binder (``create_var_apps_node``);
* the abstract-refinement higher-order ``Array.map`` / ``reduce`` -- function
  arguments like ``(x:{v:a | p v}) -> {w:b | q w}``
  (``create_abstraction_node`` / ``create_application_node``);
* ``Array.get`` -- ``i: {n:Int | n < size arr}``; and
* ``!= 0`` refinements (``Math.fmod``'s divisor) whose interval is a sympy
  ``Union`` with no single-range metahandler (``refinements.py``).

``create_grammar`` used to abort with ``KeyError`` / ``NotImplementedError`` /
``TypeError`` on these; it now skips the types it cannot represent and builds a
grammar from the rest.
"""

from aeon.core.types import top
from aeon.synthesis.grammar.grammar_generation import create_grammar
from aeon.synthesis.identification import get_holes_info
from aeon.utils.name import Name
from tests.driver import check_and_return_core


def _grammar_for_hole(code: str):
    term, ctx, _ectx, _metadata = check_and_return_core(code)
    holes = get_holes_info(ctx, term, top, [], refined_types=True)
    assert holes, "expected the program to contain a hole"
    _hole_name, (ty, hole_ctx) = next(iter(holes.items()))
    # Must not raise (previously KeyError / NotImplementedError / TypeError).
    return create_grammar(hole_ctx, ty, Name("synth", 0), {})


def test_inline_dependent_refinement_on_sibling_binder_does_not_crash():
    # ``hi``'s refinement mentions the sibling binder ``lo`` (mirrors Math.clamp).
    code = """
def clampish (x: Int) (lo: Int) (hi: {v:Int | v >= lo}) : Int = lo;

def synth (n: Int) : Int = ?hole;
"""
    assert _grammar_for_hole(code) is not None


def test_inline_nonzero_refinement_does_not_crash():
    # ``!= 0`` yields a sympy Union with no single-range metahandler.
    code = """
def recip_guard (x: {v:Int | v != 0}) : Int = x;

def synth (n: Int) : Int = ?hole;
"""
    assert _grammar_for_hole(code) is not None


def test_open_math_library_does_not_crash():
    # Brings clamp (sibling-binder refinement), refined-arrow helpers, and
    # ``!= 0`` divisor refinements into scope.
    code = """open Math

def synth (x: Float) : Float = ?hole;
"""
    assert _grammar_for_hole(code) is not None


def test_higher_order_library_use_does_not_crash():
    # A helper that *uses* the abstract-refinement higher-order ``Array.reduce``
    # together with ``Math.absf`` monomorphizes their refined-arrow types into
    # the hole's context, exercising the abstraction/application node builders.
    code = """open Array
open Math

def total_error (f: (a0:Float) -> Float) (xs: (Array Float)) : Float =
    Array.reduce (fun v => fun acc => Math.absf (f v) + acc) 0.0 xs;

def synth (x: Float) : Float = ?hole;
"""
    assert _grammar_for_hole(code) is not None
