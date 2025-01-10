from __future__ import annotations

from aeon.core.types import Type
from aeon.typechecking.context import EmptyContext
from aeon.typechecking.context import TypingContext
from aeon.typechecking.context import VariableBinder
from aeon.typechecking.well_formed import wellformed


def build_context(ls: dict[str, Type]) -> TypingContext:
    e: TypingContext = EmptyContext()
    for k in ls.keys():
        assert wellformed(e, ls[k])
        e = VariableBinder(e, k, ls[k])
    return e
