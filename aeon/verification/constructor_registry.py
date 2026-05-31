"""Registry of inductive constructor groups for SMT distinctness assertions.

Populated during inductive expansion (desugar) and consumed during SMT
translation so that Z3 ``Distinct(...)`` is asserted for constructor
constants of the same inductive type.
"""

from __future__ import annotations

# Maps inductive type name -> set of prefixed constructor constant names
# e.g. {"Pizza": {"Pizza_pepperoni", "Pizza_margherita", ...}}
_constructor_groups: dict[str, set[str]] = {}


def register_constructors(type_name: str, constructor_names: list[str]) -> None:
    _constructor_groups[type_name] = set(constructor_names)


def get_constructor_groups() -> dict[str, set[str]]:
    return _constructor_groups


def clear_constructor_registry() -> None:
    _constructor_groups.clear()
