"""Registry of inductive constructor groups for SMT distinctness assertions.

Populated during inductive expansion (desugar) and consumed during SMT
translation so that Z3 ``Distinct(...)`` is asserted for constructor
constants of the same inductive type.
"""

from __future__ import annotations

# Maps inductive type name -> ordered prefixed constructor constant names
# e.g. {"IntList": ["IntList_empty", "IntList_cons"]}
_constructor_groups: dict[str, list[str]] = {}


def register_constructors(type_name: str, constructor_names: list[str]) -> None:
    _constructor_groups[type_name] = list(constructor_names)


def get_constructor_groups() -> dict[str, set[str]]:
    return {name: set(ctors) for name, ctors in _constructor_groups.items()}


def get_constructor_order(type_name: str) -> list[str] | None:
    return _constructor_groups.get(type_name)


def clear_constructor_registry() -> None:
    _constructor_groups.clear()
