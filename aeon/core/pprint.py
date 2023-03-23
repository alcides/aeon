from __future__ import annotations

from aeon.core.liquid import LiquidLiteralBool
from aeon.core.types import AbstractionType
from aeon.core.types import BaseType
from aeon.core.types import RefinedType
from aeon.core.types import Type
from aeon.core.types import type_free_term_vars
from aeon.core.types import TypeVar


def pretty_print(t: Type) -> str:
    if isinstance(t, BaseType):
        return str(t)
    elif isinstance(t, TypeVar):
        return str(t)
    elif isinstance(t, AbstractionType):
        at = pretty_print(t.var_type)
        rt = pretty_print(t.type)
        if t.var_name in type_free_term_vars(t.var_type):
            return f"({t.var_name}:{at}) -> {rt}"
        else:
            return f"{at} -> {rt}"
    elif isinstance(t, RefinedType):
        it = pretty_print(t.type)
        if t.refinement == LiquidLiteralBool(True):
            return it
        else:
            return f"{{{t.name}:{it} | {t.refinement}}}"
    assert False
