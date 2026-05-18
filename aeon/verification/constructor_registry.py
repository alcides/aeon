"""Registry of inductive constructor groups for SMT distinctness assertions.

Thin re-export of the Rust core. The registry lives in
``aeon-rs/src/constructor_registry.rs`` so `smt_z3` can read it without a
Python round-trip per leaf translation.
"""

from __future__ import annotations

from aeon_rs import register_constructors as register_constructors
