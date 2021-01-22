from typing import Dict
from aeon.core.types import Type
from aeon.typing.context import EmptyContext, VariableBinder, TypingContext


def build_context(ls: Dict[str, Type]) -> TypingContext:
    e: TypingContext = EmptyContext()
    for k in ls.keys():
        e = VariableBinder(e, k, ls[k])
    return e