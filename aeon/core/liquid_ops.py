from __future__ import annotations

from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidTerm
from aeon.core.types import TypeConstructor, TypeVar, t_bool, t_int, t_set
from aeon.utils.name import Name


def tv(name: str) -> TypeVar:
    return TypeVar(Name(name))


liquid_prelude: dict[Name, list[TypeConstructor | TypeVar]] = {
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
    # SMT Set operations
    Name("Set_sng", 0): [t_int, t_set],
    Name("Set_cup", 0): [t_set, t_set, t_set],
    Name("Set_cap", 0): [t_set, t_set, t_set],
    Name("Set_dif", 0): [t_set, t_set, t_set],
    Name("Set_mem", 0): [t_int, t_set, t_bool],
    Name("Set_sub", 0): [t_set, t_set, t_bool],
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


def mk_liquid_or(e1: LiquidTerm, e2: LiquidTerm) -> LiquidTerm:
    if e1 == LiquidLiteralBool(True) or e2 == LiquidLiteralBool(True):
        return LiquidLiteralBool(True)
    elif e1 == LiquidLiteralBool(False):
        return e2
    elif e2 == LiquidLiteralBool(False):
        return e1
    else:
        return LiquidApp(Name("||", 0), [e1, e2])
