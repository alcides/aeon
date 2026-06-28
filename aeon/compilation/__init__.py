"""Compilation units: independent per-module compilation with .aec caching.

Naming contract
---------------
- **Surface (Lean-like syntax):** ``import M``, ``open M``, ``M.f``, bare locals.
- **Sugar (after desugar):** only ``SVar``; cross-module symbols are flat
  ``Module_bare`` strings; locals and main defs stay bare.
- **Core:** only ``Var(Name)``; no import scopes or ``SQualifiedVar``.
"""

from aeon.compilation.compile import (
    compile_and_link,
    compile_and_link_program,
    compile_file,
    compile_program,
    clear_unit_cache,
    dependency_units_for,
)
from aeon.compilation.link import link_compiled_units
from aeon.compilation.unit import CompiledUnit, ModuleExport
from aeon.sugar.desugar import build_module_scopes

__all__ = [
    "CompiledUnit",
    "ModuleExport",
    "build_module_scopes",
    "compile_and_link",
    "compile_and_link_program",
    "compile_file",
    "compile_program",
    "clear_unit_cache",
    "dependency_units_for",
    "link_compiled_units",
]
