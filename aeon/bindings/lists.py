"""Conversions at the boundary between Python and Aeon's immutable List."""

from collections.abc import Iterable, Iterator
from typing import Any


def from_iterable(values: Iterable[Any]) -> tuple:
    result: tuple = ("List_nil",)
    for value in reversed(list(values)):
        result = ("List_cons", value, result)
    return result


def iter_list(value: tuple) -> Iterator[Any]:
    while isinstance(value, tuple) and len(value) == 3 and value[0] == "List_cons":
        yield value[1]
        value = value[2]
    if value != ("List_nil",):
        raise ValueError("expected an Aeon List")


def to_list(value: tuple) -> list[Any]:
    return list(iter_list(value))
