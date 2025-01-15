from __future__ import annotations

from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidTerm
from aeon.core.types import BaseType, TypeVar

liquid_prelude: dict[str, list[BaseType | TypeVar]] = {
    "==": [TypeVar("a"), TypeVar("a"),
           BaseType("Bool")],
    "!=": [TypeVar("a"), TypeVar("a"),
           BaseType("Bool")],
    "<": [TypeVar("a"), TypeVar("a"),
          BaseType("Bool")],  # TODO typeclasses: order
    "<=": [TypeVar("a"), TypeVar("a"),
           BaseType("Bool")],
    ">": [TypeVar("a"), TypeVar("a"),
          BaseType("Bool")],
    ">=": [TypeVar("a"), TypeVar("a"),
           BaseType("Bool")],
    "-->": [BaseType("Bool"),
            BaseType("Bool"),
            BaseType("Bool")],
    "&&": [BaseType("Bool"),
           BaseType("Bool"),
           BaseType("Bool")],
    "||": [BaseType("Bool"),
           BaseType("Bool"),
           BaseType("Bool")],
    "+": [TypeVar("a"), TypeVar("a"), TypeVar("a")],
    "-": [TypeVar("a"), TypeVar("a"), TypeVar("a")],
    "*": [TypeVar("a"), TypeVar("a"), TypeVar("a")],
    "/": [TypeVar("a"), TypeVar("a"), TypeVar("a")],
    "%": [BaseType("Int"), BaseType("Int"),
          BaseType("Int")],
    "!": [BaseType("Bool"), BaseType("Bool")],
}

ops = [x for x in liquid_prelude]


def mk_liquid_and(e1: LiquidTerm, e2: LiquidTerm):
    if e1 == LiquidLiteralBool(True):
        return e2
    elif e2 == LiquidLiteralBool(True):
        return e1
    elif e1 == LiquidLiteralBool(False):
        return e1
    elif e2 == LiquidLiteralBool(False):
        return e2
    else:
        return LiquidApp("&&", [e1, e2])
