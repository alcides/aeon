"""Regression: opening a socket must yield a fresh handle on every use within a
single evaluation.

``stream_socket`` / ``dgram_socket`` take a ``Unit`` argument so that each
``stream_socket unit`` is an *application* that re-runs the native constructor.
They used to be nullary ``def``s (``def stream_socket : ... = native "..."``),
which the evaluator memoizes — so every ``let 1 s = stream_socket`` in one
evaluation aliased the SAME Python socket, and the second server's ``bind()``
ran on the first, already-closed, socket → ``OSError: [Errno 9] Bad file
descriptor``. The linear type system assumes each use is a fresh resource; the
runtime must match.

These tests open two sockets in a single evaluation and require the program to
run to completion. They do a real (loopback, ephemeral-port) bind, so they
exercise the actual syscall path the memoization broke.
"""

from __future__ import annotations

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SilentSynthesisUI


def _run(source: str):
    setup_logger()
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=False)
    driver = AeonDriver(cfg)
    errors = list(driver.parse(aeon_code=source))
    assert errors == [], errors
    return driver.run()


def test_two_tcp_servers_in_one_evaluation_get_fresh_sockets():
    src = """
open Socket

def loopback : {a : SockAddr | ipv4_sock_addr a == true} = ipv4_addr "127.0.0.1" 0

def two_servers (u : Int) : Bool =
    let 1 a0 = stream_socket unit in
    let 1 a1 = stream_bind loopback a0 in
    let done_a = stream_close a1 in
    let 1 b0 = stream_socket unit in
    let 1 b1 = stream_bind loopback b0 in
    let done_b = stream_close b1 in
    true;

def main (i : Int) : Bool = two_servers i;
"""
    # Before the fix this raised OSError (bad file descriptor) on b0's bind.
    assert _run(src) is True


def test_repeated_calls_each_open_a_fresh_socket():
    # The same constructor used across several independent calls in one
    # evaluation must hand back a different live socket each time.
    src = """
open Socket

def loopback : {a : SockAddr | ipv4_sock_addr a == true} = ipv4_addr "127.0.0.1" 0

def bind_close (u : Int) : Bool =
    let 1 s0 = stream_socket unit in
    let 1 s1 = stream_bind loopback s0 in
    let done = stream_close s1 in
    true;

def main (i : Int) : Bool =
    let a = bind_close i in
    let b = bind_close i in
    let c = bind_close i in
    a && b && c;
"""
    assert _run(src) is True


def test_two_udp_sockets_in_one_evaluation_get_fresh_sockets():
    src = """
open Socket

def loopback : {a : SockAddr | ipv4_sock_addr a == true} = ipv4_addr "127.0.0.1" 0

def two_dgram (u : Int) : Bool =
    let 1 a0 = dgram_socket unit in
    let 1 a1 = dgram_bind loopback a0 in
    let done_a = dgram_close a1 in
    let 1 b0 = dgram_socket unit in
    let 1 b1 = dgram_bind loopback b0 in
    let done_b = dgram_close b1 in
    true;

def main (i : Int) : Bool = two_dgram i;
"""
    assert _run(src) is True
