"""Registry of inductive constructor groups for SMT distinctness assertions.

Populated during inductive expansion (desugar) and consumed during SMT
translation so that Z3 ``Distinct(...)`` is asserted for constructor
constants of the same inductive type. Also stores LLVM layout hints
(type-parameter arity and per-constructor field type skeletons) and
LH-style **measure** names (``List_size``) for recursive Z3 definitions.
"""

from __future__ import annotations
from dataclasses import dataclass, field

from aeon.compilation.session import SessionMapping, current_session


@dataclass
class ConstructorRegistry:
    groups: dict[str, list[str]] = field(default_factory=dict)
    parameter_counts: dict[str, int] = field(default_factory=dict)
    fields: dict[str, list[str]] = field(default_factory=dict)
    measures: dict[str, list[str]] = field(default_factory=dict)


# Maps inductive type name -> ordered prefixed constructor constant names
# e.g. {"IntList": ["IntList_empty", "IntList_cons"]}
_constructor_groups = SessionMapping(lambda: current_session().state(ConstructorRegistry).groups)

# Number of type parameters per inductive (List=1, Pair=2, Individual=0).
_type_param_counts = SessionMapping(lambda: current_session().state(ConstructorRegistry).parameter_counts)

# Prefixed ctor name -> field type skeletons.
# Each entry is either a concrete type name ("Int", "Individual") or a
# type-parameter index as "#0", "#1", …
_constructor_fields = SessionMapping(lambda: current_session().state(ConstructorRegistry).fields)

# Inductive type name -> canonical measure names (for example ``List_size``).
_measures = SessionMapping(lambda: current_session().state(ConstructorRegistry).measures)


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


def register_measures(type_name: str, measure_names: list[str]) -> None:
    """Record LH-style measures declared with ``+ size …`` on an inductive."""
    _measures[type_name] = list(measure_names)


def get_constructor_groups() -> dict[str, set[str]]:
    return {name: set(ctors) for name, ctors in _constructor_groups.items()}


def get_constructor_order(type_name: str) -> list[str] | None:
    return _constructor_groups.get(type_name)


def get_type_param_count(type_name: str) -> int:
    return _type_param_counts.get(type_name, 0)


def get_constructor_fields(ctor_name: str) -> list[str] | None:
    return _constructor_fields.get(ctor_name)


def get_measures(type_name: str) -> list[str]:
    return list(_measures.get(type_name, []))


def is_registered_measure(name: str) -> bool:
    """Whether ``name`` (binder-id / ``__spec__`` stripped by caller) is a measure."""
    for names in _measures.values():
        if name in names:
            return True
    return False


def clear_constructor_registry() -> None:
    _constructor_groups.clear()
    _type_param_counts.clear()
    _constructor_fields.clear()
    _measures.clear()
    # Keep SMT datatype / sort caches in sync so a fresh inductive registration
    # is not shadowed by a stale Z3 Datatype from a previous program.
    try:
        from aeon.verification import smt as smt_mod

        smt_mod.clear_smt_caches()
    except ImportError:
        pass
