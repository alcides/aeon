from typing import Tuple
from aeon.ast import Literal, TypedNode, Var, If
from aeon.types import BasicType, TypeAbstraction, TypingContext, Type, t_b, t_i, star, UnionType
from aeon.typechecker.subtyping import is_subtype
from aeon.typechecker.liquefaction import liquefy, liquefy_ctx, liquefy_type
from aeon.typechecker.type_simplifier import further_reduce_type


class TypeCheckingError(Exception):
    pass


def synth_type_lit(ctx: TypingContext, e: Literal) -> Type:
    return liquefy_type(ctx, e.type)


def synth_type_var(ctx: TypingContext, e: Var) -> Type:
    return ctx.variables[e.name]


def synth_type_if(ctx: TypingContext, e: If) -> Type:
    check_type_local(ctx, e.cond, t_b)
    t1 = synth_type(ctx, e.then)
    t2 = synth_type(ctx, e.otherwise)
    return UnionType(t1, t2)


def synth_type(ctx: TypingContext, e: TypedNode) -> Type:
    if isinstance(e, Literal):
        return synth_type_lit(ctx, e)
    elif isinstance(e, Var):
        return synth_type_var(ctx, e)
    elif isinstance(e, If):
        return synth_type_if(ctx, e)
        #return TypeAbstraction("t", star, BasicType("t")) #
    raise Exception("Not implemented yet")


def check_type_local(ctx: TypingContext, e: TypedNode,
                     expected_t: Type) -> bool:
    t = synth_type(ctx, e)
    return is_subtype(ctx, t, expected_t)


def check_type(ctx: TypingContext, e: TypedNode, expected_t: Type) -> bool:
    c = liquefy_ctx(ctx.with_uninterpreted())
    t = liquefy_type(c, expected_t)
    return check_type_local(c, e, t)
