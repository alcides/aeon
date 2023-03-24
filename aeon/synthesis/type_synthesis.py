from __future__ import annotations

from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidLiteralString
from aeon.core.liquid import LiquidTerm
from aeon.core.liquid import LiquidVar
from aeon.core.liquid_ops import all_ops
from aeon.core.types import AbstractionType
from aeon.core.types import base
from aeon.core.types import BaseType
from aeon.core.types import RefinedType
from aeon.core.types import t_bool
from aeon.core.types import t_int
from aeon.core.types import t_string
from aeon.synthesis.choice_manager import ChoiceManager
from aeon.synthesis.exceptions import NoMoreBudget
from aeon.synthesis.sources import RandomSource
from aeon.typechecking.context import TypingContext
from aeon.typechecking.well_formed import inhabited

DEFAULT_DEPTH = 5
MAX_STRING_SIZE = 12


def synth_liquid_var(
    man: ChoiceManager,
    r: RandomSource,
    ctx: TypingContext,
    ty: BaseType,
    d: int = DEFAULT_DEPTH,
) -> LiquidTerm | None:
    generated = [v for (v, t) in ctx.vars() if base(t) == ty]
    options = [lambda: x for x in generated]

    if options:
        v = man.choose_rule(r, options, d)
        return LiquidVar(v)
    else:
        raise NoMoreBudget()


def synth_liquid_literal(
    man: ChoiceManager,
    r: RandomSource,
    ctx: TypingContext,
    ty: BaseType,
    d: int = DEFAULT_DEPTH,
) -> LiquidTerm:
    if ty == t_bool:
        return r.choose([LiquidLiteralBool(True), LiquidLiteralBool(False)])
    elif ty == t_int:
        i = r.next_integer()
        return LiquidLiteralInt(i)
    elif ty == t_string:
        rstring = str(
            [chr(r.next_integer()) for _ in range(r.next_integer() % MAX_STRING_SIZE)],
        )
        return LiquidLiteralString(rstring)
    else:
        raise NoMoreBudget()


def valid_ops(ty):
    return [p for p in all_ops if BaseType(p[1][-1]) == ty or str(p[1][-1]).islower()]


def synth_liquid_app(
    man: ChoiceManager,
    r: RandomSource,
    ctx: TypingContext,
    ty: BaseType,
    d: int = DEFAULT_DEPTH,
) -> LiquidTerm:
    assert isinstance(ty, BaseType)

    (name, namet) = r.choose(valid_ops(ty))
    args = []
    bindings = {"Int": t_int, "Bool": t_bool}
    for t in namet[:-1]:
        if t not in bindings:
            bindings[t] = r.choose([t_int, t_bool])
        args.append(synth_liquid(man, r, ctx, bindings[t], d - 1))
    return LiquidApp(name, args)


def synth_liquid(
    man: ChoiceManager,
    r: RandomSource,
    ctx: TypingContext,
    ty: BaseType,
    d: int = DEFAULT_DEPTH,
) -> LiquidTerm:
    assert isinstance(ty, BaseType)

    def go_liquid_var():
        return synth_liquid_var(man, r, ctx, ty, d)

    def go_liquid_lit():
        return synth_liquid_literal(man, r, ctx, ty, d)

    def go_liquid_app():
        return synth_liquid_app(man, r, ctx, ty, d)

    options = [
        go_liquid_lit,
    ]
    if valid_ops(ty):
        options.append(go_liquid_var)
    if d > 0:
        options.append(go_liquid_app)

    while man.budget > 0:
        man.checkpoint()
        k = man.choose_rule(r, options, d)
        if k:
            return k
        else:
            man.undo_choice()
    nt = go_liquid_lit()
    if nt:
        return nt
    assert False


def synth_native(
    man: ChoiceManager,
    r: RandomSource,
    ctx: TypingContext,
    d: int = DEFAULT_DEPTH,
):
    def lc_int():
        return t_int

    def lc_bool():
        return t_bool

    return man.choose_rule(r, [lc_int, lc_bool], d)


def synth_refined(
    man: ChoiceManager,
    r: RandomSource,
    ctx: TypingContext,
    d: int = DEFAULT_DEPTH,
):
    name = ctx.fresh_var()
    base = synth_native(man, r, ctx, d)
    while man.budget > 0:
        man.checkpoint()
        liquidExpr: LiquidTerm = synth_liquid(
            man,
            r,
            ctx.with_var(name, base),
            t_bool,
            d - 1,
        )
        t = RefinedType(name, base, liquidExpr)
        if inhabited(ctx, t):
            return t
        else:
            man.undo_choice()
    raise NoMoreBudget()


def synth_abstraction(
    man: ChoiceManager,
    r: RandomSource,
    ctx: TypingContext,
    d: int = DEFAULT_DEPTH,
):
    name = ctx.fresh_var()
    arg_type = synth_type(man, r, ctx, d - 1)
    ty = synth_type(man, r, ctx.with_var(name, arg_type), d - 1)
    return AbstractionType(name, arg_type, ty)


def synth_type(
    man: ChoiceManager,
    r: RandomSource,
    ctx: TypingContext,
    d: int = DEFAULT_DEPTH,
):
    def go_native():
        return synth_native(man, r, ctx, d)

    def go_refined():
        return synth_refined(man, r, ctx, d)

    def go_abst():
        return synth_abstraction(man, r, ctx, d)

    if d > 0:
        options = [
            go_native,
            # go_refined,
            # go_abst,
        ]
        return man.choose_rule(r, options, d)
    else:
        return synth_native(man, r, ctx, d)
