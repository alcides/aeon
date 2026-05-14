"""Type-level substitution and instantiation. The recursive walks live in
the Rust core (aeon_rs); this module re-exports them.
"""

from __future__ import annotations

from aeon_rs import type_substitution as type_substitution
from aeon_rs import type_variable_instantiation as type_variable_instantiation
