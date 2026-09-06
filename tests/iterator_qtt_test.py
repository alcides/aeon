"""QTT / refinement tests for Iterator."""

from __future__ import annotations

from pathlib import Path

from aeon.facade.api import (
    LinearityError,
    LinearUnusedError,
    LiquidTypeCheckingFailedRelation,
)
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SilentSynthesisUI


def _parse(source: str):
    setup_logger()
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    return list(AeonDriver(cfg).parse(aeon_code=source))


def _errors(source: str):
    return _parse(source)


def _linearity_errors(source: str):
    return [e for e in _parse(source) if isinstance(e, LinearityError)]


def _liquid_errors(source: str):
    return [e for e in _parse(source) if isinstance(e, LiquidTypeCheckingFailedRelation)]


MAIN = """
def main (args: Int) : Unit := print "ok";
"""


def test_iterator_lifecycle_typechecks():
    src = (
        """
open Array
open Iterator
def sum_two (u: Unit) : Int :=
    let 1 xs := Array.append (Array.append (Array.new{Int} u) 3) 4 in
    let 1 it0 := from_array xs in
    let p0 := has_next it0 in
    let 1 it1 := ready_iterator p0 in
    let s0 := next it1 in
    let a := next_value s0 in
    let 1 it2 := next_iterator s0 in
    let p1 := has_next it2 in
    let 1 it3 := ready_iterator p1 in
    let s1 := next it3 in
    let b := next_value s1 in
    let 1 it4 := next_iterator s1 in
    let p2 := has_next it4 in
    let 1 it5 := exhausted_iterator p2 in
    let _ := discard it5 in
    a + b;
"""
        + MAIN
    )
    assert _errors(src) == []


def test_iterator_next_without_has_next_is_rejected():
    src = (
        """
open Array
open Iterator
def bad (u: Unit) : Int :=
    let 1 xs := Array.append (Array.new{Int} u) 1 in
    let 1 it0 := from_array xs in
    let s0 := next it0 in
    let v := next_value s0 in
    let 1 it1 := next_iterator s0 in
    let p := has_next it1 in
    let 1 it2 := exhausted_iterator p in
    let _ := discard it2 in
    v;
"""
        + MAIN
    )
    assert _liquid_errors(src) != []


def test_iterator_leak_is_rejected():
    src = (
        """
open Array
open Iterator
def leak (u: Unit) : Unit :=
    let 1 xs := Array.new{Int} u in
    let 1 it := from_array xs in
    print "ignored";
"""
        + MAIN
    )
    assert any(isinstance(e, LinearUnusedError) for e in _linearity_errors(src))


def test_iterator_example_typechecks():
    example = Path(__file__).parents[1] / "examples" / "imports" / "iterator_example.ae"
    setup_logger()
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    assert AeonDriver(cfg).parse(filename=str(example)) == []
