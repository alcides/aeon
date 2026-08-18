"""Linearity-discipline tests for the QTT Array library.

``Array`` is a ``linear type``: every binder holding an array must be at
multiplicity 1, and every transforming / reading op consumes its argument.
``copy`` is the sanctioned way to split one reference into two independent
arrays (and is refinement-parametric). These tests mirror the Socket QTT
tests in ``socket_qtt_test.py``.
"""

from __future__ import annotations

from aeon.facade.api import (
    LinearityError,
    LinearTypeNotBoundLinearlyError,
    LinearUnusedError,
    LinearUsedTooManyTimesError,
)
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SilentSynthesisUI


def _parse(source: str):
    setup_logger()
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    driver = AeonDriver(cfg)
    return list(driver.parse(aeon_code=source))


def _linearity_errors(source: str):
    return [e for e in _parse(source) if isinstance(e, LinearityError)]


def test_array_linear_chain_ok():
    """Each ``let 1`` handle is consumed once by the next op."""
    src = """
open Array

def build (n: Int) : Int :=
    let 1 a0 := append (new unit) 1 in
    let 1 a1 := append a0 2 in
    let 1 a2 := set a1 0 n in
    sum a2;

def main (args: Int) : Unit := print "ok";
"""
    assert _parse(src) == []


def test_array_unused_errors():
    """A ``let 1 a := ...`` whose handle is never consumed leaves the
    linear obligation unfulfilled."""
    src = """
open Array

def leak (args: Int) : Int :=
    let 1 a := append (new unit) 1 in
    0;

def main (args: Int) : Unit := print "ok";
"""
    errs = _linearity_errors(src)
    assert any(isinstance(e, LinearUnusedError) for e in errs), errs


def test_array_used_twice_errors():
    """Consuming the linear array in two different ops references the
    binder twice — the discipline that ``copy`` exists to satisfy."""
    src = """
open Array

def twice (args: Int) : Int :=
    let 1 a := append (new unit) 1 in
    let 1 b := append a 2 in
    let 1 c := append a 3 in
    sum b;

def main (args: Int) : Unit := print "ok";
"""
    errs = _linearity_errors(src)
    assert any(isinstance(e, LinearUsedTooManyTimesError) for e in errs), errs


def test_array_omega_binder_rejected():
    """Omitting the ``1`` on an array binder is itself an error now that
    ``Array`` is a ``linear type``."""
    src = """
open Array

def leak (args: Int) : Int :=
    let a := append (new unit) 1 in
    sum a;

def main (args: Int) : Unit := print "ok";
"""
    errs = _linearity_errors(src)
    assert any(isinstance(e, LinearTypeNotBoundLinearlyError) for e in errs), errs


def test_array_copy_splits_reference_ok():
    """``copy`` consumes the single linear reference once and hands back an
    ``ArrayPair`` of two independent arrays."""
    src = """
open Array

def fork (n: Int) : Int :=
    let 1 a := append (append (new unit) n) 7 in
    let p := copy a in
    let 1 left := fst_array p in
    let 1 right := snd_array p in
    sum left + length right;

def main (args: Int) : Unit := print "ok";
"""
    assert _parse(src) == []


def test_array_copy_preserves_refinement():
    """``copy`` is refinement-parametric: the element predicate rides on
    ``a<p>`` through the pair, so a projection of a positive array is still
    known to be positive."""
    src = """
open Array

def needs_pos (1 arr: (Array {v:Int | v > 0})) : Int := sum arr;

def keeps_refinement (1 a: (Array {v:Int | v > 0})) : Int :=
    let p := copy a in
    let 1 left := fst_array p in
    needs_pos left;

def main (args: Int) : Unit := print "ok";
"""
    assert _parse(src) == []
