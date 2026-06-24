"""Linearity-discipline tests for the QTT Array library.

The array-transforming operations (``append``, ``cons``, ``set``,
``reversed``, ``map``, ``filter``) take their array argument at
multiplicity 1, so a ``let 1 a := ...`` binding must be consumed exactly
once. Threading the value through a chain keeps a single live reference;
``copy`` is the sanctioned way to split one reference into two independent
arrays. These tests mirror the Socket QTT tests in ``socket_qtt_test.py``.
"""

from __future__ import annotations

from aeon.facade.api import (
    LinearityError,
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


# ---------------------------------------------------------------------------
# Happy path: thread a single reference through a chain of transforms
# ---------------------------------------------------------------------------


def test_array_linear_chain_ok():
    """Each ``let 1`` handle is consumed once by the next op; the final
    array is released into a plain ``let`` so an observer can read it."""
    src = """
open Array

def build (n: Int) : Int :=
    let 1 a0 := append new 1 in
    let 1 a1 := append a0 2 in
    let a2 := set a1 0 n in
    sum a2;

def main (args: Int) : Unit := print "ok";
"""
    assert _linearity_errors(src) == []


# ---------------------------------------------------------------------------
# Forgetting to consume a linear array should error
# ---------------------------------------------------------------------------


def test_array_unused_errors():
    """A ``let 1 a := ...`` whose handle is never consumed leaves the
    linear obligation unfulfilled."""
    src = """
open Array

def leak (args: Int) : Int :=
    let 1 a := append new 1 in
    0;

def main (args: Int) : Unit := print "ok";
"""
    errs = _linearity_errors(src)
    assert any(isinstance(e, LinearUnusedError) for e in errs), errs


# ---------------------------------------------------------------------------
# Using the same linear reference twice (aliasing the buffer) should error
# ---------------------------------------------------------------------------


def test_array_used_twice_errors():
    """Consuming the linear array in two different ops references the
    binder twice — the discipline that ``copy`` exists to satisfy."""
    src = """
open Array

def twice (args: Int) : Int :=
    let 1 a := append new 1 in
    let b := append a 2 in
    let c := append a 3 in
    sum b;

def main (args: Int) : Unit := print "ok";
"""
    errs = _linearity_errors(src)
    assert any(isinstance(e, LinearUsedTooManyTimesError) for e in errs), errs


# ---------------------------------------------------------------------------
# `copy` is the sanctioned way to obtain two independent references
# ---------------------------------------------------------------------------


def test_array_copy_splits_reference_ok():
    """``copy`` consumes the single linear reference once and hands back an
    ``ArrayPair`` of two independent arrays, both readable without further
    linear obligation."""
    src = """
open Array

def fork (n: Int) : Int :=
    let 1 a := append (append new n) 7 in
    let p := copy a in
    sum (fst_array p) + length (snd_array p);

def main (args: Int) : Unit := print "ok";
"""
    assert _linearity_errors(src) == []
