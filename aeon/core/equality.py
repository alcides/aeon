"""Alpha-equivalence equality and canonicalization for core types and
terms — re-export of the Rust core (``aeon-rs/src/core_equality.rs``)."""

from __future__ import annotations

from aeon_rs import canonicalize_type as canonicalize_type
from aeon_rs import core_liquid_equality as core_liquid_equality
from aeon_rs import core_term_equality as core_term_equality
from aeon_rs import core_type_equality as core_type_equality

__all__ = [
    "canonicalize_type",
    "core_liquid_equality",
    "core_term_equality",
    "core_type_equality",
]
