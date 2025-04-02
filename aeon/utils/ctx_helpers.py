from __future__ import annotations

from aeon.core.types import Type
from aeon.sugar.lowering import type_to_core
from aeon.typechecking.context import TypingContext
from aeon.prelude.prelude import typing_vars
from aeon.utils.name import Name


def build_context(ls: dict[Name, Type]) -> TypingContext:
    tc = TypingContext()
    for name, ty in ls.items():
        tc = tc.with_var(name, ty)
    return tc


def built_std_context(ls: dict[Name, Type] | None = None) -> TypingContext:
    data = {k: type_to_core(typing_vars[k]) for k in typing_vars}
    if ls is not None:
        data.update(ls)
    return build_context(data)
