from __future__ import annotations
from typing import Iterable

from loguru import logger

from aeon.utils.indented_logger import IndentedLogger

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
from aeon.core.terms import RefinementApplication
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
)
from aeon.typechecking.context import TypingContext
from aeon.typechecking.entailment import entailment
from aeon.typechecking.well_formed import wellformed
from aeon.verification.horn import fresh
from aeon.verification.sub import ensure_refined
from aeon.verification.sub import implication_constraint
from aeon.verification.sub import sub
from aeon.verification.vcs import Conjunction
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import LiquidConstraint
from aeon.utils.name import Name, fresh_counter

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
        case RefinementApplication(body, ty):
            return (ctrue, ty)
            # if not is_bare(ty):
            #     # Refinement Application only works on bare types.
            #     raise CoreRefinemetnApplicationRequiresBareTypesError(t, ty)
            # (c, tabs) = synth(ctx, body)
            # nty = fresh(ctx, ty)
            # k = ctx.kind_of(nty)
            # if isinstance(nty, RefinedType) and isinstance(nty.refinement, LiquidHornApplication):
            #     nty = nty.type
            #     k = ctx.kind_of(nty)
            # if isinstance(tabs, RefinimentPolymorphism):
            #     s = type_substitution(tabs.body, tabs.name, nty)
            #     if k is None or not is_compatible(k, tabs.kind):
            #         raise CoreWrongKindInRefinementApplicationError(
            #             term=t,
            #             type=nty,
            #             expected_kind=tabs.kind,
            #             actual_kind=k,
            #         )
            #     return (c, s)
        case Hole(name):
            name_a = Name(name.name, fresh_counter.fresh())
            return ctrue, TypePolymorphism(name_a, StarKind(), TypeVar(name_a))  # TODO poly: check kind
        case _:
            logger.log("SYNTH_TYPE", ("Unhandled:", t))
            logger.log("SYNTH_TYPE", ("Unhandled:", type(t)))
            assert False, f"Unhandled term {t} in synth. Type: {type(t)}"


def check(ctx: TypingContext, t: Term, ty: Type, indentedlogger: IndentedLogger = IndentedLogger()) -> Constraint:
    try:
        assert wellformed(ctx, ty)
    except AssertionError:
        indentedlogger.write(f"Type {ty} is not wellformed")
        # logger.log("AST_INFO", f"Type {ty} is not wellformed")
        raise CoreWellformnessError(ty)
    # indentedlogger.write(f"Checking {t} against type {ty}").indent("  ")
    # logger.log("AST_INFO", f"Checking {t} against type {ty}")
    match t, ty:
        case Abstraction(name, body), AbstractionType(var_name, var_type, ret):
            indentedlogger.write(f"Checking Abstraction {name} with body {body} against type {ty}").indent("  ")
            # logger.log("AST_INFO", f"Checking Abstraction {name} with body {body} against type {ty}")
            ret = substitution_in_type(ret, Var(name), var_name)
            c = check(ctx.with_var(name, var_type), body, ret, indentedlogger=indentedlogger)
            indentedlogger.dedent().write(f"Abstraction {name} with body {body} against type {ty} is wellformed")
            return implication_constraint(name, var_type, c)
        case Let(name, val, body), _:
            # logger.log("AST_INFO", f"Checking Let {name} with value {val} and body {body} against type {ty}")
            indentedlogger.write(f"Checking Let {name} with value {val} and body {body} against type {ty}").indent("  ")
            (c1, t1) = synth(ctx, val)
            nctx: TypingContext = ctx.with_var(name, t1)
            c2 = check(nctx, body, ty, indentedlogger=indentedlogger)
            indentedlogger.dedent().write(
                f"Let {name} with value {val} and body {body} against type {ty} is wellformed"
            )
            return Conjunction(c1, implication_constraint(name, t1, c2))
        case Rec(var_name, var_type, var_value, body), _:
            # logger.log("AST_INFO", f"Checking Rec {var_name} with value {var_value} and body {body} against type {ty}")
            indentedlogger.write(
                f"Checking Rec {var_name} with value {var_value} and body {body} against type {ty}"
            ).indent("  ")
            t1 = fresh(ctx, var_type)
            nrctx: TypingContext = ctx.with_var(var_name, t1)
            c1 = check(nrctx, var_value, var_type, indentedlogger=indentedlogger.indent("var "))
            c2 = check(nrctx, body, ty, indentedlogger=indentedlogger.dedent().indent("body "))
            c1 = implication_constraint(var_name, t1, c1)
            c2 = implication_constraint(var_name, t1, c2)
            indentedlogger.dedent().write(
                f"Rec {var_name} with value {var_value} and body {body} against type {ty} is wellformed"
            )
            indentedlogger.dedent()
            return Conjunction(c1, c2)
        case If(cond, then, otherwise), _:
            logger.log(
                "AST_INFO", f"Checking If with condition {cond}, then {then}, otherwise {otherwise} against type {ty}"
            )
            indentedlogger.write(
                f"Checking If with condition {cond}, then {then}, otherwise {otherwise} against type {ty}"
            ).indent("  ")
            y = Name("_cond", fresh_counter.fresh())
            liq_cond = liquefy(cond)
            assert liq_cond is not None
            if not check_type(ctx, cond, t_bool):
                raise CoreTypingRelation(ctx, cond, t_bool)
            c0 = check(ctx, cond, t_bool, indentedlogger=indentedlogger.indent("cond "))
            name_pos = Name("branch_pos", fresh_counter.fresh())
            indentedlogger.dedent()
            c1 = implication_constraint(
                y,
                RefinedType(name_pos, t_int, liq_cond),
                check(ctx, then, ty, indentedlogger=indentedlogger.indent("then ")),
            )
            name_neg = Name("branch_neg", fresh_counter.fresh())
            indentedlogger.dedent()
            c2 = implication_constraint(
                y,
                RefinedType(name_neg, t_int, LiquidApp(Name("!", 0), [liq_cond])),
                check(ctx, otherwise, ty, indentedlogger=indentedlogger.indent("otherwise ")),
            )
            indentedlogger.dedent().write(
                f"If with condition {cond}, then {then}, otherwise {otherwise} against type {ty} is wellformed"
            )
            return Conjunction(c0, Conjunction(c1, c2))
        case TypeAbstraction(name, kind, body), TypePolymorphism(var_name, var_kind, var_body):
            # logger.log("AST_INFO", f"Checking TypeAbstraction {name} with body {body} against type {ty}")
            indentedlogger.write(f"Checking TypeAbstraction {name} with body {body} against type {ty}").indent("  ")
            if var_kind == BaseKind() and kind != var_kind:
                raise CoreWrongKindInTypeApplicationError(
                    term=t,
                    type=ty,
                    actual_kind=var_kind,
                    expected_kind=var_kind,
                )
            itype = substitute_vartype(var_body, TypeVar(name), var_name)
            c = check(ctx.with_typevar(name, var_kind), body, itype, indentedlogger=indentedlogger)
            indentedlogger.dedent().write(f"TypeAbstraction {name} with body {body} against type {ty} is wellformed")
            return c
        case _:
            # logger.log("AST_INFO", f"Checking {t} against type {ty}")
            indentedlogger.write(f"Checking {t} against type {ty}").indent("  ")
            (c, s) = synth(ctx, t)
            cp = sub(ctx, s, ty)

            if cp == LiquidConstraint(LiquidLiteralBool(False)):
                raise CoreSubtypingError(ctx, t, s, ty)
            indentedlogger.dedent().write(f"Checking {t} against type {ty} is wellformed")
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


def check_type_errors(
    ctx: TypingContext,
    term: Term,
    expected_type: Type,
) -> Iterable[AeonError]:
    # logger.log("AST_INFO", f"Checking type of {term} against {expected_type}")
    indentlogger = IndentedLogger(file="logs/typechecking.log")
    if not wellformed(ctx, expected_type, indentedlogger=indentlogger):
        return [CoreWellformnessError(expected_type)]
    try:
        # logger.log("AST_INFO", f"Checking {term}")
        indentlogger.write(f"Checking {term} against type {expected_type}").indent("  ")
        constraint = check(ctx, term, expected_type, indentedlogger=indentlogger)
        # logger.log("AST_INFO", f"Constraint: {constraint}")
        indentlogger.dedent().write(f"Constraint: {constraint}")
        match entailment(ctx, constraint):
            case True:
                # logger.log("AST_INFO", f"Entailment succeeded for {term}")
                return []
            case False:
                # logger.log("AST_INFO", f"Entailment failed for {term}")
                return [CoreTypingRelation(ctx, term, expected_type)]
    except CoreTypeCheckingError as e:
        return [e]
