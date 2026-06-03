"""Tests for the SyMetric metric-program-synthesis backend.

These exercise the parts of the backend that do not depend on a live distance
metric: bottom-up component construction and refinement-guided search. In
particular, SyMetric can build values of *inductive* types (where the
grammar-based backends have a degenerate grammar and produce nothing) and drive
them to satisfy a liquid refinement via the SMT validator.
"""

from __future__ import annotations

from aeon.core.terms import Literal
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.modules.symetric import SymetricSynthesizer
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from tests.driver import check_and_return_core


def _solve(code: str, budget: float = 20.0):
    term, ctx, ectx, metadata = check_and_return_core(code)
    targets = incomplete_functions_and_holes(ctx, term)
    holes = synthesize_holes(ctx, ectx, term, targets, metadata, SymetricSynthesizer(), budget=budget)
    return holes[next(iter(holes))]


def test_factory_registers_symetric():
    assert isinstance(make_synthesizer("symetric"), SymetricSynthesizer)


def test_solves_integer_refinement():
    # Find n with n + 4 == 7; the only solution is 3.
    code = "def n : {v:Int | v + 4 == 7} = ?hole;"
    t = _solve(code, budget=15.0)
    assert isinstance(t, Literal)
    assert t.value == 3


def test_builds_inductive_value_under_refinement():
    # A system of equations as a refinement over an inductive Pair:
    #   px + py == 18 and py == 2 * px   ==>   (6, 12).
    # The grammar-based backends cannot even build a Pair here; SyMetric
    # constructs one bottom-up and the SMT validator confirms the refinement.
    code = """
inductive Pair
| mk (x:Int) (y:Int) : {p:Pair | (px p == x) && (py p == y)}
+ px (p:Pair) : Int
+ py (p:Pair) : Int

def s : {p:Pair | (px p + py p == 18) && (py p == 2 * px p)} = ?hole;
"""
    t = _solve(code, budget=30.0)
    # synthesize_holes only returns a term that passes the (SMT) validator.
    assert t is not None
