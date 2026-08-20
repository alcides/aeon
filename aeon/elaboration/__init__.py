"""Elaboration — pure re-export of the Rust core.

The original Python implementation has been ported to Rust (see
`aeon-rs/src/elaboration.rs`); this module is now a thin shim that
re-exports the algorithm + its mutable SType subclasses.
"""

from aeon_rs import Intersection as Intersection
from aeon_rs import UnificationVar as UnificationVar
from aeon_rs import Union as Union
from aeon_rs import elaborate as elaborate
from aeon_rs import elaborate_check as elaborate_check
from aeon_rs import elaborate_foralls as elaborate_foralls
from aeon_rs import elaborate_remove_unification as elaborate_remove_unification

__all__ = [
    "Intersection",
    "UnificationVar",
    "Union",
    "elaborate",
    "elaborate_check",
    "elaborate_foralls",
    "elaborate_remove_unification",
]
