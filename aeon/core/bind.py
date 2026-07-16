"""Core-level alpha-renaming / name resolution — pure re-export of the
Rust core (``aeon-rs/src/core_bind.rs``).
"""

from __future__ import annotations

from aeon_rs import bind_ids, py_bind_ctx, py_bind_lq, py_bind_term, py_bind_type

bind_ctx = py_bind_ctx
bind_lq = py_bind_lq
bind_term = py_bind_term
bind_type = py_bind_type

__all__ = ["bind_ctx", "bind_ids", "bind_lq", "bind_term", "bind_type"]
