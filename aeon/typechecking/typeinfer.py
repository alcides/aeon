"""Bidirectional refinement type checker — pure re-export of the Rust core
(``aeon-rs/src/typeinfer.rs``)."""

from __future__ import annotations

from aeon_rs import _reflected_impl_for as _reflected_impl_for
from aeon_rs import check_type as check_type
from aeon_rs import check_type_errors as check_type_errors
from aeon_rs import is_compatible as is_compatible
from aeon_rs import synth as synth
