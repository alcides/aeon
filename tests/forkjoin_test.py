"""Compile-time and runtime tests for the ``ForkJoin`` library.

Covers module scoping, QTT ownership of ``Pool`` / ``Future``, refinement
guards on worker counts and ``halves``, and a small end-to-end run of the
one-shot helpers.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from aeon.facade.api import (
    LinearityError,
    LinearUnusedError,
    LinearUsedTooManyTimesError,
)
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SilentSynthesisUI

MAIN = '\ndef main (args: Int) : Unit := print "ok";\n'
IMPORTS = """
open Array
open ForkJoin
"""


def _errors(source: str):
    setup_logger()
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    return list(AeonDriver(cfg).parse(aeon_code=source))


def _linearity_errors(source: str):
    return [error for error in _errors(source) if isinstance(error, LinearityError)]


def _run(source: str):
    setup_logger()
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(cfg)
    errs = list(driver.parse(aeon_code=source))
    assert errs == [], errs
    return driver.run()


# ---------------------------------------------------------------------------
# Module scoping
# ---------------------------------------------------------------------------


def test_forkjoin_names_are_not_in_the_global_prelude():
    errors = [str(error) for error in _errors("def probe (u: Unit) : Int := pool_workers u;" + MAIN)]
    assert any("pool_workers" in error and "does not exist" in error for error in errors), errors


def test_import_forkjoin_keeps_api_qualified():
    source = (
        """
import ForkJoin;

def open_and_close (u: Unit) : Unit :=
    let 1 p := ForkJoin.pool 2 in
    ForkJoin.shutdown p;
"""
        + MAIN
    )
    assert _errors(source) == []


def test_open_forkjoin_lifecycle_typechecks():
    source = (
        IMPORTS
        + """
def const21 (x: Unit) : Int := 21;
def demo (u: Unit) : Int :=
    let 1 p0 := pool 2 in
    let f := fork p0 const21 in
    let 1 p1 := forked_pool f in
    let 1 fut := forked_future f in
    let v := join fut in
    let _ := shutdown p1 in
    v;
"""
        + MAIN
    )
    assert _errors(source) == []


# ---------------------------------------------------------------------------
# Linearity: Pool and Future
# ---------------------------------------------------------------------------


def test_unjoined_future_errors():
    source = (
        IMPORTS
        + """
def const1 (x: Unit) : Int := 1;
def leak (u: Unit) : Unit :=
    let 1 p0 := pool 2 in
    let f := fork p0 const1 in
    let 1 p1 := forked_pool f in
    let 1 fut := forked_future f in
    shutdown p1;
"""
        + MAIN
    )
    errs = _linearity_errors(source)
    assert any(isinstance(e, LinearUnusedError) for e in errs), errs


def test_double_join_errors():
    source = (
        IMPORTS
        + """
def const1 (x: Unit) : Int := 1;
def twice (u: Unit) : Int :=
    let 1 p0 := pool 2 in
    let f := fork p0 const1 in
    let 1 p1 := forked_pool f in
    let 1 fut := forked_future f in
    let a := join fut in
    let b := join fut in
    let _ := shutdown p1 in
    a + b;
"""
        + MAIN
    )
    errs = _linearity_errors(source)
    assert any(isinstance(e, LinearUsedTooManyTimesError) for e in errs), errs


def test_unshutdown_pool_errors():
    source = (
        IMPORTS
        + """
def leak_pool (u: Unit) : Int :=
    let 1 p := pool 2 in
    0;
"""
        + MAIN
    )
    errs = _linearity_errors(source)
    assert any(isinstance(e, LinearUnusedError) for e in errs), errs


def test_double_shutdown_errors():
    source = (
        IMPORTS
        + """
def twice_shutdown (u: Unit) : Unit :=
    let 1 p := pool 2 in
    let _ := shutdown p in
    shutdown p;
"""
        + MAIN
    )
    errs = _linearity_errors(source)
    assert any(isinstance(e, LinearUsedTooManyTimesError) for e in errs), errs


# ---------------------------------------------------------------------------
# Refinements
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("workers", [0, -1, 65])
def test_invalid_worker_counts_are_rejected(workers: int):
    source = (
        IMPORTS
        + f"""
def bad (u: Unit) : Unit :=
    let 1 p := pool {workers} in
    shutdown p;
"""
        + MAIN
    )
    errs = _errors(source)
    assert errs, f"expected refinement failure for workers={workers}"


def test_halves_rejects_singleton_array():
    source = (
        IMPORTS
        + """
def bad (u: Unit) : Int :=
    let 1 xs := (Array.new{Int} unit).append 1 in
    let h := halves xs in
    let 1 left := half_left h in
    Array.length left;
"""
        + MAIN
    )
    errs = _errors(source)
    assert errs, "singleton halves should fail to prove size >= 2"


def test_halves_and_par_map_typecheck():
    source = (
        IMPORTS
        + """
def sq (x: Int) : Int := x * x;
def ok (u: Unit) : Int :=
    let 1 xs0 := ((Array.new{Int} unit).append 1).append 2 in
    let 1 xs1 := Array.append xs0 3 in
    let h := halves xs1 in
    let 1 left := half_left h in
    let 1 right := half_right h in
    let 1 mapped := par_map 2 sq left in
    Array.length mapped + Array.length right;
"""
        + MAIN
    )
    assert _errors(source) == []


# ---------------------------------------------------------------------------
# Runtime
# ---------------------------------------------------------------------------


def test_parallel2_and_par_map_run():
    source = """
open Array
open ForkJoin

def left (x: Unit) : Int := 20;
def right (y: Unit) : Int := 22;
def inc (x: Int) : Int := x + 1;

def main (_: Int) : Int :=
    let j := parallel2 2 left right in
    let 1 xs0 := ((Array.new{Int} unit).append 1).append 2 in
    let 1 xs1 := Array.append xs0 3 in
    let 1 ys := par_map 2 inc xs1 in
    joined_fst j + joined_snd j + Array.length ys;
"""
    assert _run(source) == 45


def test_fork_join_shutdown_run():
    source = """
open ForkJoin

def const21 (x: Unit) : Int := 21;

def main (_: Int) : Int :=
    let 1 p0 := pool 2 in
    let f := fork p0 const21 in
    let 1 p1 := forked_pool f in
    let 1 fut := forked_future f in
    let v := join fut in
    let _ := shutdown p1 in
    v * 2;
"""
    assert _run(source) == 42


def test_example_files_typecheck_and_run():
    root = Path(__file__).resolve().parents[1] / "examples" / "ffi"
    for name in ("forkjoin_example.ae", "forkjoin_divide.ae"):
        source = (root / name).read_text()
        setup_logger()
        cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0)
        driver = AeonDriver(cfg)
        errs = list(driver.parse(aeon_code=source))
        assert errs == [], (name, errs)
        driver.run()
