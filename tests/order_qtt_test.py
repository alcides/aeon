"""QTT / refinement tests for the Order typestate library."""

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


def test_order_full_lifecycle_typechecks():
    src = (
        """
open Order
def flow (u: Unit) : Int :=
    let 1 o0 := new_order u in
    let 1 o1 := add_item "book" 15 o0 in
    let 1 o2 := add_item "mug" 10 o1 in
    let 1 o3 := pay 424242 o2 in
    let 1 o4 := add_gift o3 in
    let 1 o5 := ship "1 Main St" o4 in
    finalize o5;
"""
        + MAIN
    )
    assert _errors(src) == []


def test_order_gift_below_threshold_is_rejected():
    src = (
        """
open Order
def bad (u: Unit) : Int :=
    let 1 o0 := new_order u in
    let 1 o1 := add_item "pen" 5 o0 in
    let 1 o2 := pay 1 o1 in
    let 1 o3 := add_gift o2 in
    let 1 o4 := ship "here" o3 in
    finalize o4;
"""
        + MAIN
    )
    assert _liquid_errors(src) != []


def test_order_ship_before_pay_is_rejected():
    src = (
        """
open Order
def bad (u: Unit) : Int :=
    let 1 o0 := new_order u in
    let 1 o1 := add_item "book" 25 o0 in
    let 1 o2 := ship "here" o1 in
    finalize o2;
"""
        + MAIN
    )
    assert _liquid_errors(src) != []


def test_order_zero_price_item_is_rejected():
    src = (
        """
open Order
def bad (u: Unit) : Int :=
    let 1 o0 := new_order u in
    let 1 o1 := add_item "free" 0 o0 in
    let 1 o2 := pay 1 o1 in
    let 1 o3 := ship "here" o2 in
    finalize o3;
"""
        + MAIN
    )
    assert _liquid_errors(src) != []


def test_order_leak_is_rejected():
    src = (
        """
open Order
def leak (u: Unit) : Unit :=
    let 1 o := new_order u in
    print "ignored";
"""
        + MAIN
    )
    assert any(isinstance(e, LinearUnusedError) for e in _linearity_errors(src))


def test_order_example_typechecks():
    example = Path(__file__).parents[1] / "examples" / "imports" / "order_example.ae"
    setup_logger()
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    assert AeonDriver(cfg).parse(filename=str(example)) == []
