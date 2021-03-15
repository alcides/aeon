from aeon.synthesis.sources import RandomSource
from aeon.core.types import AbstractionType, RefinedType, Type, t_int, t_bool, BaseType
from aeon.core.liquid import (
    LiquidApp,
    LiquidLiteralBool,
    LiquidLiteralInt,
    LiquidTerm,
    LiquidVar,
)
from aeon.core.liquid_ops import all_ops
from aeon.typing.context import TypingContext


def base(ty: Type) -> Type:
    if isinstance(ty, RefinedType):
        return ty.type
    return ty


def synth_liquid_var(r: RandomSource, ctx: TypingContext, ty: BaseType) -> LiquidTerm:
    options = [v for (v, t) in ctx.vars() if base(t) == ty]
    if options:
        v = r.choose(options)
        return LiquidVar(v)
    else:
        return None


def synth_liquid_literal(
    r: RandomSource, ctx: TypingContext, ty: BaseType
) -> LiquidTerm:
    if ty == t_bool:
        return r.choose([LiquidLiteralBool(True), LiquidLiteralBool(False)])
    elif ty == t_int:
        i = r.next_integer()
        return LiquidLiteralInt(i)
    else:
        assert False


def synth_liquid_app(r: RandomSource, ctx: TypingContext, ty: BaseType) -> LiquidTerm:
    assert isinstance(ty, BaseType)

    valid_ops = [
        p for p in all_ops if BaseType(p[1][-1]) == ty or str(p[1][-1]).islower()
    ]

    (name, _, arg_type) = r.choose(valid_ops)

    # TODO - HERE - preencher as variaveis livres do tipo

    if arg_type is None:
        arg_type = r.choose([t_int, t_bool])
    a = synth_liquid(r, ctx, arg_type)
    b = synth_liquid(r, ctx, arg_type)
    return LiquidApp(name, [a, b])


# TODO: Type and LiquidType?
def synth_liquid(r: RandomSource, ctx: TypingContext, ty: BaseType) -> LiquidTerm:
    for i in range(100):
        k = r.choose(
            [
                lambda: synth_liquid_var(r, ctx, ty),
                lambda: synth_liquid_literal(r, ctx, ty),
                lambda: synth_liquid_app(r, ctx, ty),
            ]
        )()
        if k:
            return k
    assert False


def synth_native(r: RandomSource, ctx: TypingContext):
    return r.choose([t_int, t_bool])


def synth_refined(r: RandomSource, ctx: TypingContext):
    name = ctx.fresh_var()
    base = synth_native(r, ctx)
    liquidExpr: LiquidTerm = synth_liquid(r, ctx.with_var(name, base), t_bool)
    return RefinedType(name, base, liquidExpr)


def synth_abstraction(r: RandomSource, ctx: TypingContext):
    name = ctx.fresh_var()
    arg_type = synth_type(r, ctx)
    ty = synth_type(r, ctx.with_var(name, arg_type))
    return AbstractionType(name, arg_type, ty)


def synth_type(r: RandomSource, ctx: TypingContext):
    options = [
        lambda: synth_native(r, ctx),
        lambda: synth_refined(r, ctx),
        lambda: synth_abstraction(r, ctx),
    ]
    k = r.choose(options)()
    print("DEBUG: ", k)
    return k
