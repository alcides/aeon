from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt, LiquidVar
from typing import List
from aeon.typing.context import TypingContext, VariableBinder
from aeon.core.terms import Term, Literal, Var, Application, Abstraction
from aeon.core.types import AbstractionType, RefinedType, Type, t_int, t_bool


class InferenceError(Exception):
    pass


class Restriction(object):
    pass


class SubtypingRestriction(Restriction):
    sub: Type
    sup: Type

    def __init__(self, sub: Type, sup: Type):
        self.sub = sub
        self.sup = sup


class InferenceContext(object):
    type: Type
    restrictions: List[Restriction]

    def __init__(self, type: Type, restrictions: List[Restriction] = None):
        self.type = type
        self.restrictions = restrictions or []


IC = InferenceContext


def singleton(t: Literal) -> RefinedType:
    if t.type == t_int:
        cons = LiquidLiteralInt(t.value)
    elif t.type == t_bool:
        cons = LiquidLiteralBool(t.value)
    else:
        return t.value
    name = "lit_{}".format(t.value)
    refinement = LiquidApp("eq", [LiquidVar(name), cons])
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
    elif isinstance(t, Abstraction):
        return synth_type_abs(ctx, t)
    else:
        assert False
