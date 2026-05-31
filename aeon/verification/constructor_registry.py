"""Registry of inductive constructor groups for SMT distinctness
assertions — re-export of the Rust core
(``aeon-rs/src/constructor_registry.rs``)."""

from __future__ import annotations

from aeon_rs import clear_constructor_registry as clear_constructor_registry
from aeon_rs import get_constructor_groups as get_constructor_groups
from aeon_rs import register_constructors as register_constructors

__all__ = [
    "clear_constructor_registry",
    "get_constructor_groups",
    "register_constructors",
]
