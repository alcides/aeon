"""A-normal form / partial-evaluation pass — pure re-export of the Rust
core (``aeon-rs/src/normal_form.rs``)."""

from __future__ import annotations

from aeon_rs import nf, normal_form, optimize

__all__ = ["nf", "normal_form", "optimize"]
