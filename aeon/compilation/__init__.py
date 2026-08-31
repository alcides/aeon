"""Compilation units: independent per-module compilation with .aec caching.

Naming contract
---------------
- **Surface (Lean-like syntax):** ``import M``, ``open M``, ``M.f``, bare locals.
- **Sugar (after desugar):** only ``SVar``; cross-module symbols are flat
  ``Module_bare`` strings; locals and main defs stay bare.
- **Core:** only ``Var(Name)``; no import scopes or ``SQualifiedVar``.
"""

__all__: list[str] = []
