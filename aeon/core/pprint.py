"""Core pretty-printer — pure re-export of the Rust core
(``aeon-rs/src/core_pprint.rs``)."""

from __future__ import annotations

from aeon_rs import (
    aeon_prelude_ops_to_text,
    custom_preludes_ops_representation,
    operator_name,
    pretty_print,
    pretty_print_term,
)

__all__ = [
    "aeon_prelude_ops_to_text",
    "custom_preludes_ops_representation",
    "operator_name",
    "pretty_print",
    "pretty_print_term",
]
