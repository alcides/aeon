"""Built-in operator type signatures and short-circuiting smart
constructors — pure re-export of the Rust core
(``aeon-rs/src/liquid_ops.rs``)."""

from __future__ import annotations

from aeon_rs import liquid_prelude, mk_liquid_and, mk_liquid_or

ops = list(liquid_prelude)

__all__ = ["liquid_prelude", "mk_liquid_and", "mk_liquid_or", "ops"]
