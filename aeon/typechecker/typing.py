import copy

from ..types import TypingContext, Type, BasicType, RefinedType, AbstractionType, TypeAbstraction, \
    TypeApplication, Kind, AnyKind, star, TypeException, t_b, t_delegate, t_i, bottom, t_s, t_f
from ..ast import Var, TAbstraction, TApplication, Application, Abstraction, \
    If, Literal, TypedNode, TypeDeclaration, Definition, Program, Hole, TypeAlias

from .kinding import check_kind
from .subtyping import is_subtype
from .exceptions import TypingException
from .substitutions import substitution_expr_in_type, substitution_type_in_type, \
    substitution_expr_in_expr, substitution_type_in_expr
from .type_simplifier import reduce_type
from .zed import is_satisfiable

from aeon.translator import translate

import logging


def is_not_inhabited(ctx: TypingContext, T: Type):
    if isinstance(T, RefinedType):
        nctx = ctx.with_var(T.name, T.type)
        return not is_satisfiable(nctx, T.cond)
    else:
        return not is_satisfiable(ctx, Literal(True, t_b))


class TypeCheckingError(TypingException):
    pass



def t_base(ctx: TypingContext, e: Literal) -> Type:
    # Literals are pre-populated with their correct type from the front-end
    v = e.value
    name = "lit_b_{}".format(v)
    if ctx.inside_refinement:
        if isinstance(e.value, bool):
            return t_b
        if isinstance(e.value, int):
            return t_i
        if isinstance(e.value, float):
            return t_f
        if isinstance(e.value, str):
            return t_s

    if isinstance(e.value,
                  bool) and not e.type and not isinstance(e.type, RefinedType):
        return RefinedType(name=name,
                           type=t_b,
                           cond=Application(
                               Application(TApplication(Var("=="), t_b),
                                           Var(name)),
                               Literal(value=v, type=t_b, ensured=True)))
    elif isinstance(e.value, int) and not e.type:
        return RefinedType(name=name,
                           type=t_i,
                           cond=Application(
                               Application(TApplication(Var("=="), t_i),
                                           Var(name)),
                               Literal(value=v, type=t_i, ensured=True)))
    elif isinstance(e.value, float) and not e.type:
        return RefinedType(name=name,
                           type=t_f,
                           cond=Application(
                               Application(TApplication(Var("=="), t_f),
                                           Var(name)),
                               Literal(value=v, type=t_f, ensured=True)))
    elif isinstance(e.value, str) and not e.type:
        return RefinedType(name=name,
                           type=t_s,
                           cond=Application(
                               Application(TApplication(Var("=="), t_s),
                                           Var(name)),
                               Literal(value=v, type=t_s, ensured=True)))
    return e.type


def t_var(ctx: TypingContext, e: Var) -> Type:
    if e.name in ctx.variables:
        return ctx.variables[e.name]

    if e.name in ctx.uninterpreted_functions:
        return ctx.uninterpreted_functions[e.name]

    raise TypeCheckingError("Variable {} not in context".format(e))


def t_if(ctx: TypingContext, e: If) -> Type:
    check_type(ctx, e.cond, t_b)
    ctxThen = ctx.with_cond(e.cond)
    ctxElse = ctx.with_cond(Application(Var("!"), e.cond))

    T = synth_type(ctxThen, e.then)
    U = synth_type(ctxElse, e.otherwise)
    return SumType(T, U)


def t_abs(ctx: TypingContext, e: Abstraction) -> Type:
    nctx = ctx.with_var(e.arg_name, e.arg_type)
    body_type = synth_type(nctx, e.body)
    return AbstractionType(e.arg_name, e.arg_type, body_type)


def t_app(ctx: TypingContext, e: Application) -> Type:
    F = reduce_type(ctx, synth_type(ctx, e.target))
    if not isinstance(F, AbstractionType) and F != bottom:
        raise TypeCheckingError(
            "Application requires a function: {} : {} in {}".format(
                e.target, F, e))
    if F is bottom:
        e.argument.type = F
        return F
    T = check_type(ctx, e.argument, F.arg_type)
    return substitution_expr_in_type(F.return_type, e.argument, F.arg_name)


def t_tapp(ctx: TypingContext, e: TApplication) -> Type:
    V = reduce_type(ctx, synth_type(ctx, e.target))
    if not isinstance(V, TypeAbstraction):
        raise TypeCheckingError(
            "TypeApplication requires a Type abstraction: {} : {} in {}".
            format(e.target, V, e))


    check_kind(ctx, e.argument, V.kind)
    k = substitution_type_in_type(V.type, e.argument, V.name)
    return k


def t_tabs(ctx: TypingContext, e: TAbstraction) -> Type:
    T = synth_type(ctx.with_type_var(e.typevar, e.kind), e.body)
    return TypeAbstraction(e.typevar, e.kind, T)

holes = []


def t_hole(ctx: TypingContext, e: Hole) -> Type:
    e.type = bottom if e.type is None else e.type
    holes.append((ctx.copy(), e))
    return e.type


def synth_type(ctx: TypingContext, e: TypedNode) -> Type:
    """ Γ ⸠ e => T """
    if isinstance(e, Literal):
        t = t_base(ctx, e)
    elif isinstance(e, Var):
        t = t_var(ctx, e)
    elif isinstance(e, If):
        t = t_if(ctx, e)
    elif isinstance(e, Abstraction):
        t = t_abs(ctx, e)
    elif isinstance(e, Application):
        t = t_app(ctx, e)
    elif isinstance(e, TApplication):
        t = t_tapp(ctx, e)
    elif isinstance(e, TAbstraction):
        t = t_tabs(ctx, e)
    elif isinstance(e, Hole):
        t = t_hole(ctx, e)
    else:
        raise TypeCheckingError(
            "{} (of node type {}) does not have a type synthesis rule".format(
                e, type(e)))
    e.type = t
    return t


def check_type(ctx: TypingContext, e: TypedNode, expected: Type):
    """ Γ ⸠ e <= T """
    t = synth_type(ctx, e)
    print("inferred", t, "for", e, "expected", expected)
    if not is_subtype(ctx, t, expected):
        raise TypeCheckingError("{}:{} does not have expected type {}".format(
            translate(e), translate(t), translate(expected)))
    elif e.type == None and t != None:
        e.type = t
    return t


"""Wrapper structures"""


def check_program(ast):  # pragma: no cover
    holed = []

    def internal_check(ctx: TypingContext, e: TypedNode):

        if isinstance(e, Program):
            for decl in e.declarations:

                holes.clear()  # Reset to add holes of curr decl.
                # print("decl", decl)
                internal_check(ctx, decl)
                if holes:
                    holed.append((decl, holes.copy()))  # Append the holes

        elif isinstance(e, Definition):
            logging.debug(f"Checking the Definition: {e.name}")
            if isinstance(e.body, Var) and e.body.name == 'uninterpreted':
                check_type(ctx, e.body, e.type)
                ctx.uninterpreted_functions[e.name] = e.type
            else:
                ctx.variables[e.name] = e.type  # supports recursion
                check_type(ctx, e.body, e.type)
                ctx.variables[e.name] = e.type  # refines type
                check_kind(ctx, e.type, AnyKind())
        elif isinstance(e, TypeAlias):
            logging.debug(f"Checking the TypeAlias: {e}")
            ctx.type_aliases[e.name] = e.type
        elif isinstance(e, TypeDeclaration):
            logging.debug(f"Checking the TypeDeclaration: {e}")
            name = e.name
            kind = e.kind
            ctx.add_type_var(name, kind)  # Fixed
        else:
            logging.error(f"TypeChecking ignoring:{e} of type {type(e)}")

    ctx = TypingContext()
    ctx.setup()
    internal_check(ctx, ast)

    return ast, ctx, holed
