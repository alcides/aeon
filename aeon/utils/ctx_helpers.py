from __future__ import annotations

from aeon.core.types import Type
from aeon.sugar.lowering import type_to_core
from aeon.typechecking.context import EmptyContext
from aeon.typechecking.context import TypingContext
from aeon.typechecking.context import VariableBinder
from aeon.typechecking.well_formed import wellformed
from aeon.prelude.prelude import typing_vars


def build_context(ls: dict[str, Type]) -> TypingContext:
    e: TypingContext = EmptyContext()
    for k in ls.keys():
        assert wellformed(e, ls[k])
        e = VariableBinder(e, k, ls[k])
    return e


def built_std_context(ls: dict[str, Type] | None = None) -> TypingContext:
    data = {k: type_to_core(typing_vars[k]) for k in typing_vars}
    if ls is not None:
        data.update(ls)
    return build_context(data)
