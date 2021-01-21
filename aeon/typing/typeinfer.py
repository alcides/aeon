from typing import Tuple

from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt, LiquidVar
from aeon.core.terms import Abstraction, Application, Let, Literal, Term, Var
from aeon.core.types import AbstractionType, RefinedType, Type, t_bool, t_int
from aeon.typing.context import TypingContext, VariableBinder
from aeon.typing.subtyping import InferenceContext, Restriction, is_subtype


class InferenceError(Exception):
    pass


class SubtypingRestriction(Restriction):
    sub: Type
    sup: Type

    def __init__(self, sub: Type, sup: Type):
        self.sub = sub
        self.sup = sup


IC = InferenceContext


def singleton(t: Literal) -> RefinedType:
    if t.type == t_int:
        cons = LiquidLiteralInt(t.value)
    elif t.type == t_bool:
        cons = LiquidLiteralBool(t.value)
    else:
        return t.value
    name = "lit_{}".format(t.value)
    refinement = LiquidApp("==", [LiquidVar(name), cons])
    return RefinedType(name, t.type, refinement)


def synth_type_lit(ctx: TypingContext, t: Literal) -> InferenceContext:
    return IC(singleton(t))


def synth_type_var(ctx: TypingContext, t: Var) -> InferenceContext:
    ty = ctx.type_of(t.name)
    if ty is None:
        raise InferenceError("{} is not in context".format(t.name))
    return IC(ty)


def synth_type_app(ctx: TypingContext, t: Application) -> InferenceContext:
    tfun = synth_type(ctx, t.fun).type  # TODO extract IC
    targ = synth_type(ctx, t.arg).type  # TODO extract IC
    if isinstance(tfun, AbstractionType):
        return IC(tfun.type,
                  restrictions=[SubtypingRestriction(targ, tfun.var_type)])
    else:
        raise InferenceError("{} is not a function, but {}".format(
            t.fun, tfun))


def synth_type_abs(ctx: TypingContext, t: Abstraction) -> InferenceContext:
    nctx = VariableBinder(ctx, t.var_name, t.var_type)
    body_type = synth_type(nctx, t.body).type  # TODO extract IC
    return IC(AbstractionType(t.var_name, t.var_type, body_type))


def synth_type(ctx: TypingContext, t: Term) -> InferenceContext:
    if isinstance(t, Literal):
        return synth_type_lit(ctx, t)
    elif isinstance(t, Var):
        return synth_type_var(ctx, t)
    elif isinstance(t, Application):
        return synth_type_app(ctx, t)
    # elif isinstance(t, Abstraction):
    #    return synth_type_abs(ctx, t)
    else:
        raise InferenceError("Could not synthesize the type of ({})".format(t))


def check_type(ctx: TypingContext, t: Term,
               ty: Type) -> Tuple[bool, InferenceContext]:
    if isinstance(t, Abstraction) and isinstance(ty, AbstractionType):
        return check_type(ctx.with_var(t.var_name, ty.var_type), t.body)
    elif isinstance(t, Let):
        t1 = synth_type(ctx, t.var_value)
        return check_type(ctx.with_var(t.var_name, t1), t.body)
    else:
        try:
            ic = synth_type(ctx, t)
            return (is_subtype(ctx, ic.type, ty), ic)
        except:
            return (False, None)
