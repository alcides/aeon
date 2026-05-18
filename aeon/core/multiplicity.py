"""QTT multiplicity semiring — pure re-export of the Rust core
(``aeon-rs/src/multiplicity.rs``).

The four singletons ``M0``, ``M1``, ``MOmega``, ``MN`` are the same
``Multiplicity`` instances on every import (matched by identity from
both Python and Rust call sites).
"""

from __future__ import annotations

from aeon_rs import M0, M1, MN, MOmega, Multiplicity, add, mul
from aeon_rs import multiplicity_from_token as from_token

__all__ = ["M0", "M1", "MN", "MOmega", "Multiplicity", "add", "from_token", "mul"]
