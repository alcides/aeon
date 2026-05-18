"""Name-resolution / binding pass for sugar AST — pure re-export of the
Rust core (``aeon-rs/src/bind.rs``)."""

from __future__ import annotations

from aeon_rs import bind, bind_program, py_bind_ectx, py_bind_sterm

bind_ectx = py_bind_ectx
bind_sterm = py_bind_sterm

__all__ = ["bind", "bind_ectx", "bind_program", "bind_sterm"]
