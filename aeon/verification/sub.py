"""Subtyping → constraint generation.

Thin re-export of the Rust core (``aeon_rs``). The actual subtyping logic
lives in ``aeon-rs/src/sub.rs``.
"""

from __future__ import annotations

from aeon_rs import implication_constraint as implication_constraint
from aeon_rs import sub as sub
