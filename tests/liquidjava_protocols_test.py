"""QTT / refinement tests for Lock, Reader, Email, and Downloader."""

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


# ── Lock ──────────────────────────────────────────────────────────────────


def test_lock_lifecycle_typechecks():
    src = (
        """
open Lock
def critical (u: Unit) : Unit :=
    let 1 l0 := new_lock u in
    let 1 l1 := acquire l0 in
    let 1 l2 := release l1 in
    destroy l2;
"""
        + MAIN
    )
    assert _errors(src) == []


def test_lock_leak_is_rejected():
    src = (
        """
open Lock
def leak (u: Unit) : Unit :=
    let 1 l := new_lock u in
    print "ignored";
"""
        + MAIN
    )
    assert any(isinstance(e, LinearUnusedError) for e in _linearity_errors(src))


def test_lock_double_acquire_is_rejected():
    src = (
        """
open Lock
def bad (u: Unit) : Unit :=
    let 1 l0 := new_lock u in
    let 1 l1 := acquire l0 in
    let 1 l2 := acquire l1 in
    let 1 l3 := release l2 in
    destroy l3;
"""
        + MAIN
    )
    assert _liquid_errors(src) != []


def test_lock_example_typechecks():
    example = Path(__file__).parents[1] / "examples" / "imports" / "lock_example.ae"
    setup_logger()
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    assert AeonDriver(cfg).parse(filename=str(example)) == []


# ── Reader ────────────────────────────────────────────────────────────────


def test_reader_lifecycle_typechecks():
    src = (
        """
open Reader
def once (path: {p: String | p != ""}) : Int :=
    let 1 r0 := open_reader path in
    let step := read r0 in
    let code := read_code step in
    let 1 r1 := read_reader step in
    let _ := close r1 in
    code;
"""
        + MAIN
    )
    assert _errors(src) == []


def test_reader_unclosed_is_rejected():
    src = (
        """
open Reader
def leak (path: {p: String | p != ""}) : Unit :=
    let 1 r := open_reader path in
    print "ignored";
"""
        + MAIN
    )
    assert any(isinstance(e, LinearUnusedError) for e in _linearity_errors(src))


def test_reader_example_typechecks():
    example = Path(__file__).parents[1] / "examples" / "imports" / "reader_example.ae"
    setup_logger()
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    assert AeonDriver(cfg).parse(filename=str(example)) == []


# ── Email ─────────────────────────────────────────────────────────────────


def test_email_fluent_build_typechecks():
    src = (
        """
open Email
def compose (u: Unit) : String :=
    let 1 e0 := new_email u in
    let 1 e1 := set_from "a@x.com" e0 in
    let 1 e2 := add_to "b@x.com" e1 in
    let 1 e3 := set_body "hi" e2 in
    build e3;
"""
        + MAIN
    )
    assert _errors(src) == []


def test_email_build_without_body_is_rejected():
    src = (
        """
open Email
def bad (u: Unit) : String :=
    let 1 e0 := new_email u in
    let 1 e1 := set_from "a@x.com" e0 in
    let 1 e2 := add_to "b@x.com" e1 in
    build e2;
"""
        + MAIN
    )
    assert _liquid_errors(src) != []


def test_email_example_typechecks():
    example = Path(__file__).parents[1] / "examples" / "imports" / "email_example.ae"
    setup_logger()
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    assert AeonDriver(cfg).parse(filename=str(example)) == []


# ── Downloader ────────────────────────────────────────────────────────────


def test_downloader_lifecycle_typechecks():
    src = (
        """
open Downloader
def download (u: Unit) : Unit :=
    let 1 d0 := new_downloader u in
    let 1 d1 := start d0 in
    let 1 d2 := update d1 50 in
    let 1 d3 := update d2 100 in
    let 1 d4 := finish d3 in
    discard d4;
"""
        + MAIN
    )
    assert _errors(src) == []


def test_downloader_finish_before_100_is_rejected():
    src = (
        """
open Downloader
def bad (u: Unit) : Unit :=
    let 1 d0 := new_downloader u in
    let 1 d1 := start d0 in
    let 1 d2 := update d1 50 in
    let 1 d3 := finish d2 in
    discard d3;
"""
        + MAIN
    )
    assert _liquid_errors(src) != []


def test_downloader_non_monotonic_update_is_rejected():
    src = (
        """
open Downloader
def bad (u: Unit) : Unit :=
    let 1 d0 := new_downloader u in
    let 1 d1 := start d0 in
    let 1 d2 := update d1 80 in
    let 1 d3 := update d2 40 in
    let 1 d4 := update d3 100 in
    let 1 d5 := finish d4 in
    discard d5;
"""
        + MAIN
    )
    assert _liquid_errors(src) != []


def test_downloader_leak_is_rejected():
    src = (
        """
open Downloader
def leak (u: Unit) : Unit :=
    let 1 d := new_downloader u in
    print "ignored";
"""
        + MAIN
    )
    assert any(isinstance(e, LinearUnusedError) for e in _linearity_errors(src))


def test_downloader_example_typechecks():
    example = Path(__file__).parents[1] / "examples" / "imports" / "downloader_example.ae"
    setup_logger()
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    assert AeonDriver(cfg).parse(filename=str(example)) == []
