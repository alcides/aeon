"""Fixed-width property signatures for scalar/ADT BUSTLE tasks.

Each property aggregates across examples to AllFalse (-1), Mixed (0), or
AllTrue (1). Non-applicable type combinations and padded inputs use 2, so
absence never masquerades as Mixed. Input slots preserve parameter order.
"""

from __future__ import annotations

import math
from collections.abc import Callable, Sequence
from typing import Any, TypeAlias

from aeon.synthesis.modules.bustle.values import depth, identity, is_adt, nodes, subtree

MAX_INPUTS = 3
SIGNATURE_VERSION = 2
Scalar: TypeAlias = int | bool | str | tuple["Scalar", ...]

UNARY: tuple[tuple[type, Callable[[Any], bool]], ...] = (
    (int, lambda x: x == 0),
    (int, lambda x: x == 1),
    (int, lambda x: x < 0),
    (int, lambda x: x > 0),
    (int, lambda x: x % 2 == 0),
    (str, lambda x: x == ""),
    (str, lambda x: " " in x),
    (str, lambda x: x.isdigit()),
    (str, lambda x: x.isalpha()),
    (str, lambda x: x.islower()),
    (str, lambda x: x.isupper()),
    (str, lambda x: x == x.strip()),
    (str, lambda x: len(x) <= 3),
    (bool, lambda x: x),
    (tuple, lambda x: len(x) == 1),
    (tuple, lambda x: depth(x) <= 2),
    (tuple, lambda x: depth(x) <= 4),
    (tuple, lambda x: nodes(x) <= 3),
    (tuple, lambda x: nodes(x) <= 7),
)

BINARY: tuple[tuple[type, type, Callable[[Any, Any], bool]], ...] = (
    (int, int, lambda x, y: x == y),
    (int, int, lambda x, y: x < y),
    (int, int, lambda x, y: abs(x - y) <= 1),
    (int, int, lambda x, y: x * 2 == y),
    (str, str, lambda x, y: x == y),
    (str, str, lambda x, y: x in y),
    (str, str, lambda x, y: y in x),
    (str, str, lambda x, y: y.startswith(x)),
    (str, str, lambda x, y: y.endswith(x)),
    (str, str, lambda x, y: x.lower() in y.lower()),
    (str, str, lambda x, y: len(x) == len(y)),
    (str, str, lambda x, y: len(x) < len(y)),
    (int, str, lambda x, y: x == len(y)),
    (str, int, lambda x, y: len(x) == y),
    (bool, bool, lambda x, y: x == y),
    (tuple, tuple, lambda x, y: identity(x) == identity(y)),
    (tuple, tuple, lambda x, y: x[0] == y[0]),
    (tuple, tuple, lambda x, y: depth(x) == depth(y)),
    (tuple, tuple, lambda x, y: depth(x) < depth(y)),
    (tuple, tuple, lambda x, y: nodes(x) == nodes(y)),
    (tuple, tuple, lambda x, y: subtree(x, y)),
    (tuple, tuple, lambda x, y: subtree(y, x)),
    (int, tuple, lambda x, y: x == depth(y)),
    (tuple, int, lambda x, y: depth(x) == y),
)

FEATURE_COUNT = MAX_INPUTS * (len(UNARY) + len(BINARY)) + 2 * len(UNARY) + len(BINARY)


def aggregate(results: Sequence[bool]) -> int:
    if not results:
        return 2
    if all(results):
        return 1
    if not any(results):
        return -1
    return 0


def unary_signature(values: Sequence[Scalar]) -> tuple[int, ...]:
    return tuple(
        aggregate([predicate(v) for v in values])
        if all(type(v) is typ and (typ is not tuple or is_adt(v)) for v in values) and values
        else 2
        for typ, predicate in UNARY
    )


def pair_signature(values: Sequence[Scalar], outputs: Sequence[Scalar]) -> tuple[int, ...]:
    if len(values) != len(outputs):
        raise ValueError("property signatures require equal example counts")
    return tuple(
        aggregate([predicate(v, o) for v, o in zip(values, outputs)])
        if values
        and all(type(v) is left and (left is not tuple or is_adt(v)) for v in values)
        and all(type(o) is right and (right is not tuple or is_adt(o)) for o in outputs)
        else 2
        for left, right, predicate in BINARY
    )


def task_signature(inputs: Sequence[Sequence[Scalar]], outputs: Sequence[Scalar]) -> tuple[int, ...]:
    if not 1 <= len(inputs) <= MAX_INPUTS or not outputs:
        raise ValueError(f"BUSTLE requires 1–{MAX_INPUTS} input columns and nonempty outputs")
    signature: list[int] = []
    for column in inputs:
        signature.extend(unary_signature(column))
        signature.extend(pair_signature(column, outputs))
    signature.extend([2] * ((MAX_INPUTS - len(inputs)) * (len(UNARY) + len(BINARY))))
    signature.extend(unary_signature(outputs))
    return tuple(signature)


def value_signature(values: Sequence[Scalar], outputs: Sequence[Scalar]) -> tuple[int, ...]:
    return unary_signature(values) + pair_signature(values, outputs)


def valid_scalar(value: object, key: str, max_string: int = 256) -> bool:
    return (
        (key == "Int" and type(value) is int and abs(value) <= 10**9)
        or (key == "Bool" and type(value) is bool)
        or (key == "String" and type(value) is str and len(value) <= max_string)
    )


def probability_penalty(probability: float) -> int:
    """Paper §3.2: six probability bins yield the nonnegative cost 5-delta."""
    if not math.isfinite(probability) or not 0 <= probability <= 1:
        raise ValueError("BUSTLE guidance must produce finite probabilities in [0, 1]")
    return 5 - sum(probability >= boundary for boundary in (0.1, 0.2, 0.3, 0.4, 0.6))
