"""Helpers for surfacing Z3 failures in LSP diagnostics and messages."""

from __future__ import annotations

from z3.z3types import Z3Exception


def z3_exception_message(exc: Z3Exception) -> str:
    """Return a readable message from a :class:`Z3Exception`.

    Z3's C++ layer sometimes passes byte-string messages (e.g.
    ``b'ast is not an expression'``); decode those for user-facing text.
    """
    if not exc.args:
        return str(exc)
    msg = exc.args[0]
    if isinstance(msg, bytes):
        return msg.decode("utf-8", errors="replace")
    return str(msg)


def z3_diagnostic_message(exc: Z3Exception) -> str:
    return f"Z3 verification error: {z3_exception_message(exc)}"


def z3_synthesis_message(exc: Z3Exception) -> str:
    return f"Z3 verification error: {z3_exception_message(exc)}"
