from __future__ import annotations
from typing import Iterable

from loguru import logger

from aeon.core.instantiation import type_substitution
from aeon.core.liquid import LiquidApp, LiquidTerm
from aeon.core.types import LiquidHornApplication, StarKind
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralFloat
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidVar
from aeon.core.liquid_ops import ops
from aeon.core.substitutions import liquefy, substitute_vartype
from aeon.core.substitutions import substitution_in_type
from aeon.core.terms import Abstraction
from aeon.core.terms import Annotation
from aeon.core.terms import Application
from aeon.core.terms import Hole
from aeon.core.terms import If
from aeon.core.terms import Let
from aeon.core.terms import Literal
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import TypeAbstraction
from aeon.core.terms import TypeApplication
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, Kind, is_bare
from aeon.core.types import BaseKind
from aeon.core.types import TypeConstructor
from aeon.core.types import RefinedType
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.core.types import t_bool
from aeon.core.types import t_float
from aeon.core.types import t_int
from aeon.core.types import top
from aeon.core.types import type_free_term_vars
from aeon.facade.api import (
    AeonError,
    CoreInvalidApplicationError,
    CoreSubtypingError,
    CoreTypeApplicationRequiresBareTypesError,
    CoreTypeCheckingError,
    CoreTypingRelation,
    CoreVariableNotInContext,
    CoreWellformnessError,
    CoreWrongKindInTypeApplicationError,
    LiquidTypeCheckingFailedRelation,
)
from aeon.typechecking.context import TypingContext
from aeon.typechecking.entailment import entailment, entailment_context
from aeon.typechecking.well_formed import wellformed
from aeon.verification.horn import fresh
from aeon.verification.sub import ensure_refined
from aeon.verification.sub import implication_constraint
from aeon.verification.sub import sub
from aeon.verification.vcs import Conjunction
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import LiquidConstraint
from aeon.verification.horn import solve
from aeon.utils.name import Name, fresh_counter
from aeon.verification.helpers import (
    remove_unrelated_context,
    simplify_constraint,
    conjunctive_normal_form,
    is_implication_true,
)

ctrue = LiquidConstraint(LiquidLiteralBool(True))


def is_compatible(a: Kind, b: Kind):
    """Returns whether kind a is a subkind of kind b"""
    return (a == b) or b == StarKind()


def argument_is_typevar(ty: Type):
    return (
        isinstance(ty, TypeVar)
        or isinstance(
            ty,
            RefinedType,
        )
        and isinstance(ty.type, TypeVar)
    )


def prim_litbool(t: bool) -> RefinedType:
    vname = Name("v", fresh_counter.fresh())
    if t:
        return RefinedType(vname, t_bool, LiquidVar(vname))
    else:
        return RefinedType(vname, t_bool, LiquidApp(Name("!", 0), [LiquidVar(vname)]))


def prim_litint(t: int) -> RefinedType:
    vname = Name("v", fresh_counter.fresh())
    return RefinedType(
        vname,
        t_int,
        LiquidApp(Name("==", 0), [LiquidVar(vname), LiquidLiteralInt(t)]),
    )


def prim_litfloat(t: float) -> RefinedType:
    vname = Name("v", fresh_counter.fresh())
    return RefinedType(
        vname,
        t_float,
        LiquidApp(Name("==", 0), [LiquidVar(vname), LiquidLiteralFloat(t)]),
    )


def make_binary_app_type(t: Name, ity: TypeConstructor | TypeVar, oty: TypeConstructor | TypeVar) -> Type:
    """Creates the type of a binary operator"""
    xname = Name("x", fresh_counter.fresh())
    yname = Name("y", fresh_counter.fresh())
    zname = Name("z", fresh_counter.fresh())
    output = RefinedType(
        zname,
        oty,
        LiquidApp(
            Name("==", 0),
            [
                LiquidVar(zname),
                LiquidApp(
                    t,
                    [LiquidVar(xname), LiquidVar(yname)],
                ),
            ],
        ),
    )
    appt2 = AbstractionType(yname, ity, output)
    appt1 = AbstractionType(xname, ity, appt2)
    return appt1


def prim_op(t: Name) -> Type:
    match t.name:
        case "%":
            return make_binary_app_type(t, t_int, t_int)
        case "+" | "-" | "*" | "/":
            name_a = Name("a", fresh_counter.fresh())
            return TypePolymorphism(name_a, BaseKind(), make_binary_app_type(t, TypeVar(name_a), TypeVar(name_a)))
        case "==" | "!=" | ">" | ">=" | "<" | "<=":
            name_a = Name("a", fresh_counter.fresh())
            return TypePolymorphism(name_a, BaseKind(), make_binary_app_type(t, TypeVar(name_a), t_bool))
        case "&&" | "||":
            return make_binary_app_type(t, t_bool, t_bool)
        case "!":
            name = Name("fresh", fresh_counter.fresh())
            return AbstractionType(name, t_bool, t_bool)
        case _:
            assert False, f"Unknown selfication of {t}"


def rename_liquid_term(refinement: LiquidTerm, old_name: Name, new_name: Name):
    if isinstance(refinement, LiquidVar):
        if refinement.name == old_name:
            return LiquidVar(new_name)
        else:
            return refinement
    elif isinstance(refinement, LiquidLiteralBool):
        return refinement
    elif isinstance(refinement, LiquidLiteralInt):
        return refinement
    elif isinstance(refinement, LiquidLiteralFloat):
        return refinement
    elif isinstance(refinement, LiquidApp):
        return LiquidApp(
            refinement.fun,
            [rename_liquid_term(x, old_name, new_name) for x in refinement.args],
        )
    elif isinstance(refinement, LiquidHornApplication):
        if refinement.name == old_name:
            return LiquidHornApplication(
                new_name,
                [(rename_liquid_term(x, old_name, new_name), t) for (x, t) in refinement.argtypes],
            )
        else:
            return LiquidHornApplication(
                refinement.name,
                [(rename_liquid_term(x, old_name, new_name), t) for (x, t) in refinement.argtypes],
            )
    else:
        assert False


def renamed_refined_type(ty: RefinedType) -> RefinedType:
    old_name = ty.name
    new_name = Name("_inner_" + old_name.name, fresh_counter.fresh())

    refinement = rename_liquid_term(ty.refinement, old_name, new_name)
    return RefinedType(new_name, ty.type, refinement)


# patterm matching term
def synth(ctx: TypingContext, t: Term) -> tuple[Constraint, Type]:
    match t:
        case Literal(_, TypeConstructor(Name("Unit", _))):
            # TODO: Unit is encoded as True, replace with custom Sort
            return (ctrue, prim_litbool(True))
        case Literal(vb, TypeConstructor(Name("Bool", _))):
            assert isinstance(vb, bool)
            return (ctrue, prim_litbool(vb))
        case Literal(vi, TypeConstructor(Name("Int", _))):
            assert isinstance(vi, int)
            return (ctrue, prim_litint(vi))
        case Literal(vf, TypeConstructor(Name("Float", _))):
            assert isinstance(vf, float)
            return (ctrue, prim_litfloat(vf))
        case Literal(_, TypeConstructor(Name("String", _))):
            # TODO: String support
            return (ctrue, t.type)
        case Var(name):
            if name in ops:
                return (ctrue, prim_op(name))
            ty = ctx.type_of(name)
            if not ty:
                raise CoreVariableNotInContext(ctx, t)
            if isinstance(ty, TypeConstructor) or isinstance(ty, RefinedType) or isinstance(ty, TypeVar):
                ty = ensure_refined(ty)
                assert isinstance(ty, RefinedType)
                # assert ty.name != t.name
                if ty.name == t.name:
                    ty = renamed_refined_type(ty)
                # Self
                ty = RefinedType(
                    ty.name,
                    ty.type,
                    LiquidApp(
                        Name("&&", 0),
                        [
                            ty.refinement,
                            LiquidApp(
                                Name("==", 0),
                                [
                                    LiquidVar(ty.name),
                                    LiquidVar(t.name),
                                ],
                            ),
                        ],
                    ),
                )
            return (ctrue, ty)
        case Application(fun, arg):
            (c, ty) = synth(ctx, fun)
            match ty:
                case AbstractionType(aname, atype, rtype):
                    cp = check(ctx, arg, atype)
                    t_subs = substitution_in_type(rtype, arg, aname)
                    c0 = Conjunction(c, cp)
                    # if ctx.has_uninterpreted_fun(aname):
                    #     selfification = LiquidConstraint(LiquidApp(
                    #             Name("==", 0),
                    #             [
                    #                 LiquidVar(aname),
                    #                 LiquidApp(fun, []),
                    #             ],
                    #     ))
                    #     c0 = Conjunction(c0, selfification)
                    return (c0, t_subs)
                case _:
                    raise CoreInvalidApplicationError(t, ty)
        case Let(var_name, var_value, body):
            (c1, t1) = synth(ctx, var_value)
            nctx: TypingContext = ctx.with_var(var_name, t1)
            (c2, t2) = synth(nctx, body)
            term_vars = type_free_term_vars(t1)
            assert t.var_name not in term_vars
            r = (Conjunction(c1, implication_constraint(var_name, t1, c2)), t2)
            return r
        case Rec(var_name, var_type, var_value, body):
            nrctx: TypingContext = ctx.with_var(var_name, var_type)
            c1 = check(nrctx, var_value, var_type)
            (c2, t2) = synth(nrctx, body)
            c1 = implication_constraint(var_name, var_type, c1)
            c2 = implication_constraint(var_name, var_type, c2)
            return Conjunction(c1, c2), t2
        case Annotation(expr, ty):
            nty = fresh(ctx, ty)
            c = check(ctx, expr, nty)
            return c, nty
        case TypeApplication(body, ty):
            if not is_bare(ty):
                # Type Application only works on bare types.
                raise CoreTypeApplicationRequiresBareTypesError(t, ty)
            (c, tabs) = synth(ctx, body)
            nty = fresh(ctx, ty)
            k = ctx.kind_of(nty)
            if isinstance(nty, RefinedType) and isinstance(nty.refinement, LiquidHornApplication):
                nty = nty.type
                k = ctx.kind_of(nty)
            if isinstance(tabs, TypePolymorphism):
                s = type_substitution(tabs.body, tabs.name, nty)
                if k is None or not is_compatible(k, tabs.kind):
                    raise CoreWrongKindInTypeApplicationError(term=t, type=nty, expected_kind=tabs.kind, actual_kind=k)
                return (c, s)
            else:
                assert isinstance(tabs, AbstractionType)
                return (c, tabs)
        case Hole(name):
            name_a = Name(name.name, fresh_counter.fresh())
            return ctrue, TypePolymorphism(name_a, StarKind(), TypeVar(name_a))  # TODO poly: check kind
        case _:
            logger.log("SYNTH_TYPE", ("Unhandled:", t))
            logger.log("SYNTH_TYPE", ("Unhandled:", type(t)))
            assert False, f"Unhandled term {t} in synth. Type: {type(t)}"


def check(ctx: TypingContext, t: Term, ty: Type) -> Constraint:
    try:
        assert wellformed(ctx, ty)
    except AssertionError:
        raise CoreWellformnessError(ty)
    match t, ty:
        case Abstraction(name, body), AbstractionType(var_name, var_type, ret):
            ret = substitution_in_type(ret, Var(name), var_name)
            c = check(ctx.with_var(name, var_type), body, ret)
            return implication_constraint(name, var_type, c)
        case Let(name, val, body), _:
            (c1, t1) = synth(ctx, val)
            nctx: TypingContext = ctx.with_var(name, t1)
            c2 = check(nctx, body, ty)
            return Conjunction(c1, implication_constraint(name, t1, c2))
        case Rec(var_name, var_type, var_value, body), _:
            t1 = fresh(ctx, var_type)
            nrctx: TypingContext = ctx.with_var(var_name, t1)
            c1 = check(nrctx, var_value, var_type)
            c2 = check(nrctx, body, ty)
            c1 = implication_constraint(var_name, t1, c1)
            c2 = implication_constraint(var_name, t1, c2)
            return Conjunction(c1, c2)
        case If(cond, then, otherwise), _:
            y = Name("_cond", fresh_counter.fresh())
            liq_cond = liquefy(cond)
            assert liq_cond is not None
            if not check_type(ctx, cond, t_bool):
                raise CoreTypingRelation(ctx, cond, t_bool)
            c0 = check(ctx, cond, t_bool)
            name_pos = Name("branch_pos", fresh_counter.fresh())
            c1 = implication_constraint(
                y,
                RefinedType(name_pos, t_int, liq_cond),
                check(ctx, then, ty),
            )
            name_neg = Name("branch_neg", fresh_counter.fresh())
            c2 = implication_constraint(
                y,
                RefinedType(name_neg, t_int, LiquidApp(Name("!", 0), [liq_cond])),
                check(ctx, otherwise, ty),
            )
            return Conjunction(c0, Conjunction(c1, c2))
        case TypeAbstraction(name, kind, body), TypePolymorphism(var_name, var_kind, var_body):
            if var_kind == BaseKind() and kind != var_kind:
                raise CoreWrongKindInTypeApplicationError(
                    term=t,
                    type=ty,
                    actual_kind=var_kind,
                    expected_kind=var_kind,
                )
            itype = substitute_vartype(var_body, TypeVar(name), var_name)
            return check(ctx.with_typevar(name, var_kind), body, itype)
        case _:
            (c, s) = synth(ctx, t)
            cp = sub(ctx, s, ty)
            if cp == LiquidConstraint(LiquidLiteralBool(False)):
                raise CoreSubtypingError(ctx, t, s, ty)
            return Conjunction(c, cp)


def check_type(ctx: TypingContext, t: Term, ty: Type = top) -> bool:
    """Returns whether expression t has type ty in context ctx."""
    try:
        assert wellformed(ctx, ty)
        constraint = check(ctx, t, ty)
        # TODO: convert constraint to canonical form
        # constraint = canonicalize_constraint(constraint, [name for (name, _) in ctx.vars()])
        # assert wellformed_constraint(ctx, constraint), f"Constraint {constraint} not wellformed."
        v = entailment(ctx, constraint)
        return v
    except CoreTypeCheckingError:
        return False


def constraint_to_parts(c: Constraint) -> Iterable[Constraint]:
    """Prepares a constraint into a list of sub-problems for error messages"""
    for cons in conjunctive_normal_form(c):
        if not is_implication_true(cons):
            if not solve(cons):
                cons_simp = simplify_constraint(cons)
                cons_clean, _ = remove_unrelated_context(cons_simp, ignore_vars=set())
                yield cons_clean


def check_type_errors(
    ctx: TypingContext,
    term: Term,
    expected_type: Type,
) -> Iterable[AeonError]:
    if not wellformed(ctx, expected_type):
        return [CoreWellformnessError(expected_type)]

    try:
        constraint = check(ctx, term, expected_type)
        match entailment(ctx, constraint):
            case True:
                return []
            case False:
                print("term.loc:", term)
                full_constraint = entailment_context(ctx, constraint)
                return [
                    LiquidTypeCheckingFailedRelation(ctx, term, expected_type, v)
                    for v in constraint_to_parts(full_constraint)
                ]
    except CoreTypeCheckingError as e:
        return [e]
