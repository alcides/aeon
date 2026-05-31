"""Multiplicities (Quantitative Type Theory) — re-export of the Rust
core (``aeon-rs/src/multiplicity.rs``).

The four singletons (``M0`` erased, ``M1`` linear, ``MOmega`` unrestricted,
``MN`` polymorphic) are the same ``Multiplicity`` instances on every
import (matched by identity from both Python and Rust call sites).
``add`` and ``mul`` implement the QTT semiring; ``from_token`` parses a
surface-syntax token.
"""

from aeon_rs import M0 as M0
from aeon_rs import M1 as M1
from aeon_rs import MN as MN
from aeon_rs import MOmega as MOmega
from aeon_rs import Multiplicity as Multiplicity
from aeon_rs import add as add
from aeon_rs import mul as mul
from aeon_rs import multiplicity_from_token as from_token

__all__ = ["M0", "M1", "MN", "MOmega", "Multiplicity", "add", "from_token", "mul"]
