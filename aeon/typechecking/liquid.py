from __future__ import annotations

from aeon.core.liquid import LiquidApp, LiquidLiteralFloat
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidLiteralString
from aeon.core.liquid import LiquidTerm
from aeon.core.liquid import LiquidVar
from aeon.core.liquid_ops import get_type_of
from aeon.core.types import Type, t_bool
from aeon.core.types import t_float
from aeon.core.types import t_int
from aeon.core.types import t_string
from aeon.typechecking.context import TypingContext


class LiquidTypeCheckException(Exception):
    pass


def type_infer_liquid(
    ctx: TypingContext,
    liq: LiquidTerm,
) -> Type | None:
    match liq:
        case LiquidLiteralBool(_):
            return t_bool
        case LiquidLiteralInt(_):
            return t_int
        case LiquidLiteralFloat(_):
            return t_float
        case LiquidLiteralString(_):
            return t_string
        case LiquidVar(name):
            return ctx.type_of(name)
        case LiquidApp(fun, args):
            ftype = get_type_of(
                fun)  # smt.int.__plus__ instead of + in LiquidTypes

            if len(ftype) != len(args) + 1:
                raise LiquidTypeCheckException(
                    f"Function application {liq} needs {len(ftype)-1} arguments, but was passed {len(args)}."
                )

            for arg, exp_t in zip(args, ftype):
                k = type_infer_liquid(ctx, arg)
                if k != exp_t:
                    raise LiquidTypeCheckException(
                        f"Argument {arg} in {liq} is expected to be of type {exp_t}, but {k} was found instead."
                    )
            return ftype[-1]
        case _:
            assert False, f"Constructed {liq} ({type(liq)}) not supported."
