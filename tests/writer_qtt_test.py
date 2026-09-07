"""QTT / refinement tests for Writer."""

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


def test_writer_lifecycle_typechecks():
    src = (
        """
open Writer
def write_once (path: {p: String | p != ""}) : Unit :=
    let 1 w0 := open_writer path in
    let payload := payload_from_string "hello" in
    let 1 w1 := write payload w0 in
    close w1;
"""
        + MAIN
    )
    assert _errors(src) == []


def test_writer_unclosed_is_rejected():
    src = (
        """
open Writer
def leak (path: {p: String | p != ""}) : Unit :=
    let 1 w := open_writer path in
    print "ignored";
"""
        + MAIN
    )
    assert any(isinstance(e, LinearUnusedError) for e in _linearity_errors(src))


def test_writer_empty_path_is_rejected():
    src = (
        """
open Writer
def bad (u: Unit) : Unit :=
    let 1 w0 := open_writer "" in
    close w0;
"""
        + MAIN
    )
    assert _liquid_errors(src) != []


def test_writer_example_typechecks():
    example = Path(__file__).parents[1] / "examples" / "imports" / "writer_example.ae"
    setup_logger()
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    assert AeonDriver(cfg).parse(filename=str(example)) == []
