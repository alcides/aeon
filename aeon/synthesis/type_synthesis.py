from aeon.synthesis.sources import RandomSource
from aeon.core.types import (
    AbstractionType,
    RefinedType,
    Type,
    t_int,
    t_bool,
    t_string,
    BaseType,
    base,
)
from aeon.core.liquid import (
    LiquidApp,
    LiquidLiteralBool,
    LiquidLiteralInt,
    LiquidLiteralString,
    LiquidTerm,
    LiquidVar,
)
from aeon.core.liquid_ops import all_ops
from aeon.typing.context import TypingContext

DEFAULT_DEPTH = 9
MAX_STRING_SIZE = 12


def synth_liquid_var(
    r: RandomSource, ctx: TypingContext, ty: BaseType, d: int = DEFAULT_DEPTH
) -> LiquidTerm:
    options = [v for (v, t) in ctx.vars() if base(t) == ty]
    if options:
        v = r.choose(options)
        return LiquidVar(v)
    else:
        return None


def synth_liquid_literal(
    r: RandomSource, ctx: TypingContext, ty: BaseType, d: int = DEFAULT_DEPTH
) -> LiquidTerm:
    if ty == t_bool:
        return r.choose([LiquidLiteralBool(True), LiquidLiteralBool(False)])
    elif ty == t_int:
        i = r.next_integer()
        return LiquidLiteralInt(i)
    elif ty == t_string:
        rstring = str(
            [chr(r.next_integer()) for _ in range(r.next_integer() % MAX_STRING_SIZE)]
        )
        return LiquidLiteralString(rstring)
    else:
        assert False


def synth_liquid_app(
    r: RandomSource, ctx: TypingContext, ty: BaseType, d: int = DEFAULT_DEPTH
) -> LiquidTerm:
    assert isinstance(ty, BaseType)

    valid_ops = [
        p for p in all_ops if BaseType(p[1][-1]) == ty or str(p[1][-1]).islower()
    ]

    (name, namet) = r.choose(valid_ops)
    args = []
    bindings = {"Int": t_int, "Bool": t_bool}
    for t in namet[:-1]:
        if t not in bindings:
            bindings[t] = r.choose([t_int, t_bool])
        args.append(synth_liquid(r, ctx, bindings[t], d - 1))
    return LiquidApp(name, args)


# TODO: Type and LiquidType?
def synth_liquid(
    r: RandomSource, ctx: TypingContext, ty: BaseType, d: int = DEFAULT_DEPTH
) -> LiquidTerm:
    assert isinstance(ty, BaseType)

    options = [
        lambda: synth_liquid_var(r, ctx, ty, d),
        lambda: synth_liquid_literal(r, ctx, ty, d),
    ]
    if d > 0:
        options.append(lambda: synth_liquid_app(r, ctx, ty, d))

    for _ in range(100):
        k = r.choose(options)()
        if k:
            return k
    assert False


def synth_native(r: RandomSource, ctx: TypingContext, d: int = DEFAULT_DEPTH):
    return r.choose([t_int, t_bool])


def synth_refined(r: RandomSource, ctx: TypingContext, d: int = DEFAULT_DEPTH):
    name = ctx.fresh_var()
    base = synth_native(r, ctx, d)
    liquidExpr: LiquidTerm = synth_liquid(r, ctx.with_var(name, base), t_bool, d)
    return RefinedType(name, base, liquidExpr)


def synth_abstraction(r: RandomSource, ctx: TypingContext, d: int = DEFAULT_DEPTH):
    name = ctx.fresh_var()
    arg_type = synth_type(r, ctx, d)
    ty = synth_type(r, ctx.with_var(name, arg_type), d)
    return AbstractionType(name, arg_type, ty)


def synth_type(r: RandomSource, ctx: TypingContext, d: int = DEFAULT_DEPTH):
    if d > 0:
        options = [
            lambda: synth_native(r, ctx, d),
            lambda: synth_refined(r, ctx, d),
            lambda: synth_abstraction(r, ctx, d),
        ]
        return r.choose(options)()
    else:
        return synth_native(r, ctx, d)
