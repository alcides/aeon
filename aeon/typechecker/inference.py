from aeon.typechecker.liquefaction import liquefy, liquefy_ctx
from typing import Tuple, Dict, List, Optional
from functools import reduce
import copy

from ..types import TypingContext, Type, BasicType, RefinedType, IntersectionType, UnionType, AbstractionType, TypeAbstraction, \
    TypeApplication, Kind, AnyKind, star, TypeException, t_b, t_delegate, t_i, bottom, t_s, t_f, top
from ..ast import Var, TAbstraction, TApplication, Application, Abstraction, \
    If, Literal, TypedNode, TypeDeclaration, Definition, Program, Hole, TypeAlias
from aeon.typechecker.type_simplifier import reduce_type
from .subtyping import is_subtype

from .kinding import check_kind
from .ast_helpers import make_equality_bool, make_equality_int, make_equality_float, make_equality_str
from .substitutions import substitution_expr_in_type, substitution_type_in_type, \
    substitution_expr_in_expr, substitution_type_in_expr


class TypeCheckingError(Exception):
    pass


class VariableState(object):
    def __init__(self, name: str):
        self.lower_bounds = [bottom]
        self.upper_bounds = [top]
        self.name = str(name)

    def upper_limit(self):
        return reduce(IntersectionType, self.upper_bounds)

    def lower_limit(self):
        return reduce(UnionType, self.lower_bounds)

    def __str__(self):
        return "var({} l={} u={})".format(self.name, self.lower_limit(),
                                          self.upper_limit())

    def __repr__(self):
        return "var({} l={} u={})".format(self.name, self.lower_limit(),
                                          self.upper_limit())

    def is_valid(self, ctx):
        print("H", self.lower_limit(), self.upper_limit())
        return is_subtype(ctx, self.lower_limit(), self.upper_limit())


class ConstraintEnv(object):
    def __init__(self, vtt: Optional[Dict[str, VariableState]] = None):
        if vtt == None:
            vtt = {}
        self.variables_to_track: Dict[str, VariableState] = vtt

    def empty(self):
        return len(self.variables_to_track.values()) == 0

    def __repr__(self):
        return "{" + " | ".join([
            str(self.variables_to_track[k])
            for k in self.variables_to_track.keys()
        ]) + "}"


def merge_ics(d1: ConstraintEnv, d2: ConstraintEnv):
    nd = {}
    for k in d1.variables_to_track:
        if k not in nd:
            nd[k] = d1.variables_to_track[k]
    for k in d2.variables_to_track:
        if k not in nd:
            nd[k] = d2.variables_to_track[k]
    return ConstraintEnv(nd)


def infer_lit(ctx: TypingContext, e: Literal) -> Tuple[Type, ConstraintEnv]:
    x = "lit" + ctx.fresh_var()
    if isinstance(e.value, int):
        c = make_equality_int(x, e.value)
    elif isinstance(e.value, bool):
        c = make_equality_bool(x, e.value)
    elif isinstance(e.value, float):
        c = make_equality_float(x, e.value)
    elif isinstance(e.value, str):
        c = make_equality_str(x, e.value)
    else:
        return (e.type, ConstraintEnv())

    return (RefinedType(x, e.type, c), ConstraintEnv())


def infer_var(ctx: TypingContext, e: Var) -> Tuple[Type, ConstraintEnv]:
    if e.name in ctx.variables:
        return (ctx.variables[e.name], ConstraintEnv())
    elif ctx.inside_refinement and e.name in ctx.uninterpreted_functions:
        return (ctx.uninterpreted_functions[e.name], ConstraintEnv())
    else:
        raise TypeCheckingError("Variable {} not found in context".format(
            e.name))


def infer_abs(ctx: TypingContext,
              e: Abstraction) -> Tuple[Type, ConstraintEnv]:
    nctx = ctx.with_var(e.arg_name, e.arg_type)
    body_type, ic = infer(nctx, e.body)
    return (AbstractionType(e.arg_name, e.arg_type, body_type), ic)


def infer_if(ctx: TypingContext, e: If) -> Tuple[Type, ConstraintEnv]:
    b, ic = check_type_local(ctx, e.cond, t_b)
    if not b:
        raise TypeCheckingError("If condition not boolean in {}".format(e))
    ctxThen = ctx.with_cond(e.cond)
    ctxElse = ctx.with_cond(Application(Var("smtNot"), e.cond))

    T, tic = infer(ctxThen, e.then)
    U, eic = infer(ctxElse, e.otherwise)
    return (UnionType(T, U), merge_ics(ic, merge_ics(tic, eic)))


def infer_app(ctx: TypingContext,
              e: Application) -> Tuple[Type, ConstraintEnv]:
    F, fic = infer(ctx, e.target)

    if isinstance(F, AbstractionType):
        b, aic = check_type_local(ctx, e.argument, F.arg_type)
        if not b:
            raise TypeCheckingError("Argument {} not of type {}", e.argument,
                                    F.arg_type)

        t = substitution_expr_in_type(F.return_type, e.argument, F.arg_name)
        ic = merge_ics(fic, aic)
        return (t, ic)  # liquefaction? Manual, maybe?
    else:
        T, aic = infer(ctx, e.argument)
        ret_varname = "Abs" + ctx.fresh_type_var()
        argument_name = "abs" + ctx.fresh_var()
        aic.variables_to_track[ret_varname] = VariableState(ret_varname)
        t = BasicType(ret_varname)
        tchecks, tic = check_type_local(ctx, e.target,
                                        AbstractionType(ctx.fresh_var(), T, t))
        if not tchecks:
            raise TypeCheckingError("Function {} not of type {}", e.target,
                                    AbstractionType(argument_name, T, t))

        return t, merge_ics(aic, tic)


def infer_tapp(ctx: TypingContext,
               e: TApplication) -> Tuple[Type, ConstraintEnv]:
    V, fic = infer(ctx, e.target)
    if not isinstance(V, TypeAbstraction):
        raise TypeCheckingError(
            "TypeApplication requires a Type abstraction: {} : {} in {}".
            format(e.target, V, e))
    if e.argument == t_delegate:
        name = ctx.fresh_type_var()
        fic.variables_to_track[name] = VariableState(name)
        rep = BasicType(name)
    else:
        check_kind(ctx, e.argument, V.kind)
        rep = e.type
    k = substitution_type_in_type(V.type, rep, V.name)
    return (k, fic)


def infer_tabs(ctx: TypingContext,
               e: TAbstraction) -> Tuple[Type, ConstraintEnv]:
    T, ic = infer(ctx.with_type_var(e.typevar, e.kind), e.body)
    return (TypeAbstraction(e.typevar, e.kind, T), ic)


def infer(ctx: TypingContext, e: TypedNode) -> Tuple[Type, ConstraintEnv]:
    if isinstance(e, Literal):
        return infer_lit(ctx, e)
    elif isinstance(e, Var):
        return infer_var(ctx, e)
    elif isinstance(e, Abstraction):
        return infer_abs(ctx, e)
    elif isinstance(e, If):
        return infer_if(ctx, e)
    elif isinstance(e, Application):
        return infer_app(ctx, e)
    elif isinstance(e, TApplication):
        return infer_tapp(ctx, e)
    elif isinstance(e, TAbstraction):
        return infer_tabs(ctx, e)
    else:
        raise TypeCheckingError("Unknown inference rule for {}".format(e))


def constrain(t1: Type, t2: Type, constraints: Dict[str, VariableState]):
    if isinstance(t1, RefinedType):
        constrain(t1.type, t2, constraints)
        return
    if isinstance(t2, RefinedType):
        constrain(t1, t2.type, constraints)
        return
    if isinstance(t1, BasicType) and isinstance(t2, BasicType) and t1 == t2:
        return
    elif t1 == bottom:
        return
    elif t2 == top:
        return
    elif isinstance(
            t1, BasicType) and t1.name in constraints.keys() and isinstance(
                t2, BasicType) and t2.name in constraints.keys():
        constraints[t1.name].upper_bounds.append(t2)
        constraints[t2.name].lower_bounds.append(t1)
    elif isinstance(t1, BasicType) and t1.name in constraints.keys():
        constraints[t1.name].upper_bounds.append(t2)
        for t in constraints[t1.name].lower_bounds:
            constrain(t, t2, constraints)
    elif isinstance(t2, BasicType) and t2.name in constraints.keys():
        constraints[t2.name].lower_bounds.append(t1)
        for t in constraints[t2.name].upper_bounds:
            constrain(t1, t, constraints)

    elif isinstance(t1, AbstractionType) and isinstance(t2, AbstractionType):
        constrain(t2.arg_type, t1.arg_type, constraints)
        constrain(t1.return_type, t2.return_type, constraints)

    elif isinstance(t1, TypeApplication) and isinstance(t2, TypeApplication):
        constrain(t1.target, t2.target, constraints)
        constrain(t1.argument, t2.argument, constraints)  # TODO: variance?
    else:
        raise TypeCheckingError("Not a subtype!", t1, t2)


def try_unification(ctx: TypingContext, t1: Type, t2: Type,
                    ic: ConstraintEnv) -> Tuple[bool, ConstraintEnv]:
    nic = copy.copy(ic)
    constrain(t1, t2, nic.variables_to_track)
    for key in nic.variables_to_track:
        if not nic.variables_to_track[key].is_valid(ctx):
            raise TypeCheckingError("Variable impossible to exist:", key,
                                    nic.variables_to_track[key])
    return True, nic


def check_type_local(ctx: TypingContext, e: TypedNode,
                     expected_t: Type) -> Tuple[bool, ConstraintEnv]:
    (t, ic) = infer(ctx, e)
    if isinstance(e, Var) and e.name == "smtEq":
        print(" ", e, t, ic, "<:", expected_t)
    if ic.empty():
        return (is_subtype(ctx, t, expected_t), ic)
    else:
        return try_unification(ctx, t, expected_t, ic)


def check_type(ctx: TypingContext, e: TypedNode, expected_t: Type) -> bool:
    t = liquefy(ctx, expected_t)
    #try:
    (b, nic) = check_type_local(ctx, e, expected_t)
    #except TypeCheckingError:
    #return False
    return b
