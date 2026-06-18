"""Linearity-discipline tests for the QTT Socket library.

Each test exercises an opt-in scenario by defining a small program that
imports ``Socket`` and tries to use a ``StreamSocket`` either correctly
(the chain ``open → bind → listen → close``) or incorrectly (forgetting
``close``, double-close, using a stale handle after the next operation
consumed it). The expectations match the Phase 2a/2b/3 diagnostics in
``aeon.facade.api``.
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
# Happy path: the canonical lifecycle
# ---------------------------------------------------------------------------


def test_socket_open_bind_listen_close_ok():
    """``open → bind → listen → close``: each ``stream_*`` op consumes its
    socket linearly and returns a fresh linear handle that the next step
    consumes. ``stream_close`` closes the loop."""
    src = """
open Socket

def lifecycle (port: { p: Int | (p >= 0) && (p <= 65535) }) : Unit :=
    let 1 s0 := stream_socket unit in
    let 1 s1 := stream_bind (ipv4_addr "127.0.0.1" port) s0 in
    let 1 s2 := stream_listen 5 s1 in
    stream_close s2;

def main (args: Int) : Unit := print "ok";
"""
    assert _linearity_errors(src) == []


# ---------------------------------------------------------------------------
# Forgetting ``close`` should error
# ---------------------------------------------------------------------------


def test_socket_unclosed_errors():
    """``let 1 s = stream_socket`` without a downstream ``stream_close`` (or
    any other consumer) leaves the linear obligation unfulfilled."""
    src = """
open Socket

def leak (args: Int) : Unit :=
    let 1 s := stream_socket unit in
    print "ignored s";

def main (args: Int) : Unit := print "ok";
"""
    errs = _linearity_errors(src)
    assert any(isinstance(e, LinearUnusedError) for e in errs), errs


# ---------------------------------------------------------------------------
# Double-close should error
# ---------------------------------------------------------------------------


def test_socket_double_close_errors():
    """Closing the same socket twice (via the explicit binder being
    referenced twice) trips the linear ``> 1`` diagnostic."""
    src = """
open Socket

def double_close (args: Int) : Unit :=
    let 1 s := stream_socket unit in
    let _ := stream_close s in
    stream_close s;

def main (args: Int) : Unit := print "ok";
"""
    errs = _linearity_errors(src)
    assert any(isinstance(e, LinearUsedTooManyTimesError) for e in errs), errs


# ---------------------------------------------------------------------------
# Reusing a handle after an op consumed it should error
# ---------------------------------------------------------------------------


def test_socket_use_after_consume_errors():
    """``stream_listen`` consumes the bound socket and returns a *new*
    linear socket. Trying to ``stream_close`` the original ``s1`` after
    that uses the binder twice."""
    src = """
open Socket

def stale (port: { p: Int | (p >= 0) && (p <= 65535) }) : Unit :=
    let 1 s0 := stream_socket unit in
    let 1 s1 := stream_bind (ipv4_addr "127.0.0.1" port) s0 in
    let 1 s2 := stream_listen 5 s1 in
    let _ := stream_close s2 in
    stream_close s1;

def main (args: Int) : Unit := print "ok";
"""
    errs = _linearity_errors(src)
    assert any(isinstance(e, LinearUsedTooManyTimesError) for e in errs), errs


# ---------------------------------------------------------------------------
# Aliasing through `let g = s` does not bypass linearity
# ---------------------------------------------------------------------------


def test_socket_alias_then_double_close_errors():
    """Aliasing the linear socket through ``let g = s`` and closing both
    is caught by the alias projection (Phase 3)."""
    src = """
open Socket

def alias_double (args: Int) : Unit :=
    let 1 s := stream_socket unit in
    let g := s in
    let _ := stream_close s in
    stream_close g;

def main (args: Int) : Unit := print "ok";
"""
    errs = _linearity_errors(src)
    assert any(isinstance(e, LinearUsedTooManyTimesError) for e in errs), errs
