from __future__ import annotations

from aeon.core.types import Type
from aeon.typechecking.context import TypingContext
from aeon.typechecking.context import VariableBinder


def build_context(ls: dict[str, Type]) -> TypingContext:
    e: TypingContext = TypingContext()
    for k in ls.keys():
        e += VariableBinder(k, ls[k])
    return e
