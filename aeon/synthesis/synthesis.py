from aeon.core.terms import Literal
from aeon.core.types import BaseType, RefinedType, Type, t_int, t_bool
from aeon.synthesis.sources import RandomSource
from aeon.typing.context import TypingContext
from aeon.typing.typeinfer import check_type


def syntht_literal(r: RandomSource, ctx: TypingContext, ty: Type):
    if isinstance(ty, BaseType):
        if ty == t_int:
            return Literal(r.next_integer(), ty)
        elif ty == t_bool:
            return Literal(r.choice([True, False]), ty)
        else:
            assert False
    elif isinstance(ty, RefinedType):
        while True:
            k = syntht_literal(r, ctx, ty.base)
            if check_type(ctx, k, ty):
                break
        return k


def extract_base_type(ty: Type):
    if isinstance(ty, RefinedType):
        return ty.type
    else:
        return ty


def syntht(r: RandomSource, ctx: TypingContext, ty: Type):
    b = extract_base_type(ty)
    if b == t_int or b == t_bool:
        return syntht_literal(r, ctx, b)
    else:
        assert False