"""Type hierarchy — re-export of the Rust core (``aeon-rs/src/types.rs``
and ``aeon-rs/src/core_types_helpers.rs``).
"""

from __future__ import annotations

# Type hierarchy + Kind, all from Rust.
from aeon_rs import AbstractionType as AbstractionType
from aeon_rs import ExistentialType as ExistentialType
from aeon_rs import Kind as Kind
from aeon_rs import LiquidHornApplication as LiquidHornApplication
from aeon_rs import RefinedType as RefinedType
from aeon_rs import RefinementPolymorphism as RefinementPolymorphism
from aeon_rs import Top as Top
from aeon_rs import Type as Type
from aeon_rs import TypeConstructor as TypeConstructor
from aeon_rs import TypePolymorphism as TypePolymorphism
from aeon_rs import TypeVar as TypeVar

# Module-level constants and helpers (built once at Rust module init).
from aeon_rs import base as base
from aeon_rs import builtin_core_types as builtin_core_types
from aeon_rs import extract_parts as extract_parts
from aeon_rs import get_type_vars as get_type_vars
from aeon_rs import is_bare as is_bare
from aeon_rs import liq_true as liq_true
from aeon_rs import refined_to_unrefined_type as refined_to_unrefined_type
from aeon_rs import t_bool as t_bool
from aeon_rs import t_float as t_float
from aeon_rs import t_gpu_config as t_gpu_config
from aeon_rs import t_int as t_int
from aeon_rs import t_set as t_set
from aeon_rs import t_string as t_string
from aeon_rs import t_tensor as t_tensor
from aeon_rs import t_unit as t_unit
from aeon_rs import top as top
from aeon_rs import type_free_term_vars as type_free_term_vars
from aeon_rs import with_binders as with_binders

__all__ = [
    "AbstractionType",
    "ExistentialType",
    "Kind",
    "LiquidHornApplication",
    "RefinedType",
    "RefinementPolymorphism",
    "Top",
    "Type",
    "TypeConstructor",
    "TypePolymorphism",
    "TypeVar",
    "base",
    "builtin_core_types",
    "extract_parts",
    "get_type_vars",
    "is_bare",
    "liq_true",
    "refined_to_unrefined_type",
    "t_bool",
    "t_float",
    "t_gpu_config",
    "t_int",
    "t_set",
    "t_string",
    "t_tensor",
    "t_unit",
    "top",
    "type_free_term_vars",
    "with_binders",
]
