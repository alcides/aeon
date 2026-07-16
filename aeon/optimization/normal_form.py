"""A-normal form / partial-evaluation pass — re-export of the Rust
core (``aeon-rs/src/normal_form.rs``)."""

from __future__ import annotations

from aeon_rs import nf as nf
from aeon_rs import normal_form as normal_form
from aeon_rs import optimize as optimize

__all__ = ["nf", "normal_form", "optimize"]
