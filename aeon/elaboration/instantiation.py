"""Sugar-level type substitution — pure re-export of the Rust core
(``aeon-rs/src/elab_inst.rs``)."""

from __future__ import annotations

from aeon_rs import sugar_type_substitution

type_substitution = sugar_type_substitution

__all__ = ["type_substitution"]
