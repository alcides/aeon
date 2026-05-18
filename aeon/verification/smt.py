"""SMT verification surface — pure re-export of the Rust core.

Everything below — `flatten`, `smt_valid`, `uncurry` — lives in
``aeon-rs/src/smt_*.rs``. No Python implementation remains in this
module.
"""

from __future__ import annotations

from aeon_rs import flatten as flatten
from aeon_rs import smt_valid as smt_valid
from aeon_rs import uncurry as uncurry
