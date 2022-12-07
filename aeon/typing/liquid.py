from __future__ import annotations

from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidLiteralString
from aeon.core.liquid import LiquidTerm
from aeon.core.liquid import LiquidVar
from aeon.core.liquid_ops import get_type_of
from aeon.core.types import base
from aeon.core.types import BaseType
from aeon.core.types import t_bool
from aeon.core.types import t_int
from aeon.core.types import t_string
from aeon.core.types import Type
from aeon.typing.context import TypingContext


def type_infer_liquid(
    ctx: TypingContext,
    liq: LiquidTerm,
) -> Type | None:  # TODO: should be BaseType?
    if isinstance(liq, LiquidLiteralBool):
        return t_bool
    elif isinstance(liq, LiquidLiteralInt):
        return t_int
    elif isinstance(liq, LiquidLiteralString):
        return t_string
    elif isinstance(liq, LiquidVar):
        t = ctx.type_of(liq.name)
        if t:
            return base(t)
        else:
            return None
    elif isinstance(liq, LiquidApp):
        ftype = get_type_of(liq.fun)
        equalities: dict[str, BaseType] = {}
        for a, raw_t in zip(liq.args, ftype):
            t = BaseType(raw_t)
            k = type_infer_liquid(ctx, a)
            if raw_t.islower():
                if raw_t in equalities:
                    if equalities[raw_t] != k:
                        return None
                elif isinstance(k, BaseType):
                    equalities[raw_t] = k
                else:
                    return None
            else:
                if k != t:
                    return None

        rt = ftype[-1]
        if rt in equalities:
            return equalities[rt]
        return BaseType(ftype[-1])
    else:
        assert False
