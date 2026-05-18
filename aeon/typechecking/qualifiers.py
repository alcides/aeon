"""Extract finite qualifier sets (Q) from typing context and types.

Thin re-export of the Rust core. The actual implementation lives in
``aeon-rs/src/qualifiers.rs``.

Used for predicate abstraction / constrained Horn solving: unknown refinements
are searched as boolean combinations of atoms drawn from Q (see e.g. Jhala &
Vazou, "Refinement Types: A Tutorial", arXiv:2010.07763; Polikarpova et al.,
PLDI 2016 Synquid).
"""

from __future__ import annotations

from aeon_rs import extract_qualifier_atoms as extract_qualifier_atoms
