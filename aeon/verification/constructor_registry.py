"""Registry of inductive constructor groups for SMT distinctness assertions.

Populated during inductive expansion (desugar) and consumed during SMT
translation so that Z3 ``Distinct(...)`` is asserted for constructor
constants of the same inductive type. Also stores LLVM layout hints
(type-parameter arity and per-constructor field type skeletons).
"""

from __future__ import annotations

# Maps inductive type name -> ordered prefixed constructor constant names
# e.g. {"IntList": ["IntList_empty", "IntList_cons"]}
_constructor_groups: dict[str, list[str]] = {}

# Number of type parameters per inductive (List=1, Pair=2, Individual=0).
_type_param_counts: dict[str, int] = {}

# Prefixed ctor name -> field type skeletons.
# Each entry is either a concrete type name ("Int", "Individual") or a
# type-parameter index as "#0", "#1", …
_constructor_fields: dict[str, list[str]] = {}


def register_constructors(
    type_name: str,
    constructor_names: list[str],
    type_param_count: int = 0,
    field_types: dict[str, list[str]] | None = None,
) -> None:
    _constructor_groups[type_name] = list(constructor_names)
    _type_param_counts[type_name] = type_param_count
    if field_types:
        _constructor_fields.update(field_types)


def get_constructor_groups() -> dict[str, set[str]]:
    return {name: set(ctors) for name, ctors in _constructor_groups.items()}


def get_constructor_order(type_name: str) -> list[str] | None:
    return _constructor_groups.get(type_name)


def get_type_param_count(type_name: str) -> int:
    return _type_param_counts.get(type_name, 0)


def get_constructor_fields(ctor_name: str) -> list[str] | None:
    return _constructor_fields.get(ctor_name)


def clear_constructor_registry() -> None:
    _constructor_groups.clear()
    _type_param_counts.clear()
    _constructor_fields.clear()
