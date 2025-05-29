from __future__ import annotations

from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidTerm
from aeon.core.types import TypeConstructor, TypeVar, t_bool, t_int
from aeon.utils.name import Name


def tv(name: str) -> TypeVar:
    return TypeVar(Name(name))


liquid_prelude: dict[Name, list[TypeConstructor | TypeVar | TypeConstructor]] = {
    Name("==", 0): [tv("a"), tv("a"), t_bool],
    Name("!=", 0): [tv("a"), tv("a"), t_bool],
    Name("<", 0): [tv("a"), tv("a"), t_bool],  # TODO typeclasses: order
    Name("<=", 0): [tv("a"), tv("a"), t_bool],
    Name(">", 0): [tv("a"), tv("a"), t_bool],
    Name(">=", 0): [tv("a"), tv("a"), t_bool],
    Name("-->", 0): [t_bool, t_bool, t_bool],
    Name("&&", 0): [t_bool, t_bool, t_bool],
    Name("||", 0): [t_bool, t_bool, t_bool],
    Name("+", 0): [tv("a"), tv("a"), tv("a")],
    Name("-", 0): [tv("a"), tv("a"), tv("a")],
    Name("*", 0): [tv("a"), tv("a"), tv("a")],
    Name("/", 0): [tv("a"), tv("a"), tv("a")],
    Name("%", 0): [t_int, t_int, t_int],
    Name("!", 0): [t_bool, t_bool],
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
        return LiquidApp(Name("&&", 0), [e1, e2])
