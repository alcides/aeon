from __future__ import annotations

from aeon.core.types import Type
from aeon.typing.context import EmptyContext
from aeon.typing.context import TypingContext
from aeon.typing.context import VariableBinder


def build_context(ls: dict[str, Type]) -> TypingContext:
    e: TypingContext = EmptyContext()
    for k in ls.keys():
        e = VariableBinder(e, k, ls[k])
    return e
