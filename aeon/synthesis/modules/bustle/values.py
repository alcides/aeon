"""Bounded structural ADT observations; no inspection of arbitrary native objects."""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any

MAX_DEPTH = 16
MAX_NODES = 128
ConstructorSchemas = Mapping[str, Mapping[str, tuple[str, ...]]]


def is_adt(value: Any) -> bool:
    return type(value) is tuple and bool(value) and type(value[0]) is str


def depth(value: Any) -> int:
    return 1 + max((depth(field) for field in value[1:]), default=0) if is_adt(value) else 0


def nodes(value: Any) -> int:
    return 1 + sum(nodes(field) for field in value[1:]) if is_adt(value) else 0


def identity(value: Any) -> tuple:
    """Include scalar types: Python otherwise equates True and 1 inside tuples."""
    if is_adt(value):
        return ("ADT", value[0], tuple(identity(field) for field in value[1:]))
    return (type(value).__name__, value)


def subtree(child: Any, parent: Any) -> bool:
    if not is_adt(child) or not is_adt(parent):
        return False
    return identity(child) == identity(parent) or any(subtree(child, field) for field in parent[1:])


def valid_value(value: Any, key: str, schemas: ConstructorSchemas) -> bool:
    """Validate every constructor/field against the concrete instantiated DSL.

    Check bounds while traversing, before hashing or computing properties. A
    registered constructor tag alone does not validate its arity or payload.
    """
    from aeon.synthesis.modules.bustle.signatures import valid_scalar

    remaining = MAX_NODES

    def visit(current: Any, current_key: str, level: int) -> bool:
        nonlocal remaining
        if current_key not in schemas:
            return valid_scalar(current, current_key)
        if level > MAX_DEPTH or remaining <= 0 or not is_adt(current):
            return False
        remaining -= 1
        fields = schemas[current_key].get(current[0])
        return (
            fields is not None
            and len(current) == len(fields) + 1
            and all(visit(field, field_key, level + 1) for field, field_key in zip(current[1:], fields))
        )

    return visit(value, key, 1)
