import copy

from ..types import TypingContext, Type, BasicType, RefinedType, AbstractionType, TypeAbstraction, \
    TypeApplication, Kind, AnyKind, star, TypeException, t_b, t_delegate
from ..ast import Var, TAbstraction, TApplication, Application, Abstraction, \
    If, Literal, TypedNode

from .kinding import check_kind
from .conversions import type_conversion
from .subtyping import is_subtype
from .exceptions import TypingException
from .substitutions import substitution_expr_in_type, substitution_type_in_type, \
    substitution_expr_in_expr, substitution_type_in_expr
from .utils import flatten_refined_type


class TypeCheckingError(TypingException):
    pass


def t_base(ctx: TypingContext, e: Literal) -> Type:
    # Literals are pre-populated with their correct type from the front-end
    return e.type


def t_var(ctx: TypingContext, e: Var) -> Type:
    if e.name not in ctx.variables:
        raise TypeCheckingError("Variable {} not in context".format(e))
    return ctx.variables[e.name]


def t_if(ctx: TypingContext, e: If) -> Type:
    pass


def t_abs(ctx: TypingContext, e: Abstraction) -> Type:
    nctx = ctx.with_var(e.arg_name, e.arg_type)
    body_type = synth_type(nctx, e.body)
    return AbstractionType(e.arg_name, e.arg_type, body_type)


def t_app(ctx: TypingContext, e: Application) -> Type:
    # delegate hack
    # (==[???]) 1 is converted to (==[Integer]) 1
    if isinstance(e.target, TApplication):
        if e.target.argument == t_delegate:
            T = flatten_refined_type(synth_type(ctx, copy.copy(e.argument)))
            e.target.argument = T
    # end hack
    F = type_conversion(synth_type(ctx, e.target))
    if not isinstance(F, AbstractionType):
        raise TypeCheckingError(
            "Application requires a function: {} : {} in {}".format(
                e.target, F, e))
    T = check_type(ctx, e.argument, F.arg_type)

    print("hack", e.target.type, e.argument.type)
    print("Replacing:", F.return_type, e.argument, F.arg_name)
    return substitution_expr_in_type(F.return_type, e.argument, F.arg_name)


def t_tapp(ctx: TypingContext, e: TApplication) -> Type:
    V = type_conversion(synth_type(ctx, e.target))
    if not isinstance(V, TypeAbstraction):
        raise TypeCheckingError(
            "TypeApplication requires a Type abstraction: {} : {} in {}".
            format(e.target, V, e))
    check_kind(ctx, e.argument, V.kind)
    return substitution_type_in_type(V.type, e.argument, V.name)


def t_tabs(ctx: TypingContext, e: TAbstraction) -> Type:
    T = synth_type(ctx.with_type_var(e.typevar, e.kind), e.body)
    return TypeAbstraction(e.typevar, e.kind, T)


def synth_type(ctx: TypingContext, e: TypedNode) -> Type:
    """ Γ ⸠ e => T """
    if isinstance(e, Literal):
        return t_base(ctx, e)
    elif isinstance(e, Var):
        return t_var(ctx, e)
    elif isinstance(e, If):
        return t_if(ctx, e)
    elif isinstance(e, Abstraction):
        return t_abs(ctx, e)
    elif isinstance(e, Application):
        return t_app(ctx, e)
    elif isinstance(e, TApplication):
        return t_tapp(ctx, e)
    elif isinstance(e, TAbstraction):
        return t_tabs(ctx, e)
    else:
        raise TypeCheckingError(
            "{} does not have a type synthesis rule".format(e))


def check_type(ctx: TypingContext, e: TypedNode, expected: Type):
    """ Γ ⸠ e <= T """
    t = synth_type(ctx, e)
    if not is_subtype(ctx, t, expected):
        raise TypeCheckingError("{}:{} does not have expected type {}".format(
            e, t, expected))
    return t


"""Wrapper structures"""


def check_program(ast):
    if isinstance(ast, Program):
        for decl in ast.declarations:
            check_program(decl)
    else:
        print("failed in", ast, type(ast))