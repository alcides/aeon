from typing import Dict, Optional
from aeon.typing.context import TypingContext
from aeon.core.liquid import (
    LiquidApp,
    LiquidLiteralBool,
    LiquidLiteralInt,
    LiquidLiteralString,
    LiquidTerm,
    LiquidVar,
)
from aeon.core.liquid_ops import get_type_of
from aeon.core.types import BaseType, t_bool, t_int, t_string, base


def type_infer_liquid(ctx: TypingContext, liq: LiquidTerm) -> Optional[BaseType]:
    if isinstance(liq, LiquidLiteralBool):
        return t_bool
    elif isinstance(liq, LiquidLiteralInt):
        return t_int
    elif isinstance(liq, LiquidLiteralString):
        return t_string
    elif isinstance(liq, LiquidVar):
        t = ctx.type_of(liq.name)
        return base(t)
    elif isinstance(liq, LiquidApp):
        ftype = get_type_of(liq.fun)
        equalities: Dict[str, BaseType] = {}
        for (a, raw_t) in zip(liq.args, ftype):
            t = BaseType(raw_t)
            k = type_infer_liquid(ctx, a)
            if raw_t.islower():
                if raw_t in equalities:
                    if equalities[raw_t] != k:
                        return None
                else:
                    equalities[raw_t] = k
            else:
                if k != t:
                    return None

        rt = ftype[-1]
        if rt in equalities:
            return equalities[rt]
        return BaseType(ftype[-1])
    else:
        assert False
