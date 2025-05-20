from __future__ import annotations

from loguru import logger
from dataclasses import dataclass

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
from aeon.core.types import BaseType
from aeon.core.types import RefinedType
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.core.types import t_bool
from aeon.core.types import t_float
from aeon.core.types import t_int
from aeon.core.types import t_unit
from aeon.core.types import top
from aeon.core.types import type_free_term_vars
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


class TypeCheckingException(Exception):
    pass


class CouldNotGenerateConstraintException(TypeCheckingException):
    pass


@dataclass
class FailedConstraintException(TypeCheckingException):
    ctx: TypingContext
    t: Term
    ty: Type
    ks: Constraint

    def __str__(self):
        return f"Constraint violated when checking if {self.t} : {self.ty}: \n {self.ks}"


@dataclass
class WrongKindException(TypeCheckingException):
    expected: Kind
    found: Kind
    t: Term
    ty: Type

    def __str__(self):
        return f"Expected kind {self.expected}, but found kind {self.found} in {self.t} of type {self.ty}."


@dataclass
class TypeApplicationOnlyWorksOnBareTypesException(TypeCheckingException):
    t: Term
    ty: Type

    def __str__(self):
        return f"Cannot use bare types in type applications (type {self.ty} in {self.t})."


@dataclass
class WrongKindInTypeApplication(TypeCheckingException):
    t: Term
    expected: Kind
    actual: Kind | None

    def __str__(self):
        return f"Wrong kind in {self.t}. Expected {self.expected}, got {self.actual}."


@dataclass
class TypeNotWellformed(TypeCheckingException):
    ty: Type

    def __str__(self):
        return f"Type {self.ty} is not wellformed."


@dataclass
class FailedSubtypingException(TypeCheckingException):
    ctx: TypingContext
    t: Term
    s: Type
    ty: Type

    def __str__(self):
        return f"Subtyping relationship of {self.t} failed. Inferred {self.s}, got {self.ty}"


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


def make_binary_app_type(t: Name, ity: BaseType | TypeVar, oty: BaseType | TypeVar) -> Type:
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
    if isinstance(t, Literal) and t.type == t_unit:
        return (
            ctrue,
            prim_litbool(True),
        )  # TODO: Unit is encoded as True, replace with custom Sort
    elif isinstance(t, Literal) and t.type == t_bool:
        assert isinstance(t.value, bool)
        return (ctrue, prim_litbool(t.value))
    elif isinstance(t, Literal) and t.type == t_int:
        assert isinstance(t.value, int)
        return (ctrue, prim_litint(t.value))
    elif isinstance(t, Literal) and t.type == t_float:
        assert isinstance(t.value, float)
        return (ctrue, prim_litfloat(t.value))
    elif isinstance(t, Literal):
        return (ctrue, t.type)
    elif isinstance(t, Var):
        if t.name in ops:
            return (ctrue, prim_op(t.name))
        ty = ctx.type_of(t.name)
        if not ty:
            raise CouldNotGenerateConstraintException(
                f"Variable {t.name} not in context",
            )
        if isinstance(ty, BaseType) or isinstance(ty, RefinedType) or isinstance(ty, TypeVar):
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
    elif isinstance(t, Application):
        (c, ty) = synth(ctx, t.fun)
        match ty:
            case AbstractionType(aname, atype, rtype):
                cp = check(ctx, t.arg, atype)
                t_subs = substitution_in_type(rtype, t.arg, aname)
                c0 = Conjunction(c, cp)
                return (c0, t_subs)
            case _:
                raise CouldNotGenerateConstraintException(
                    f"Application {t} ({ty}) is not a function.",
                )
    elif isinstance(t, Let):
        (c1, t1) = synth(ctx, t.var_value)
        nctx: TypingContext = ctx.with_var(t.var_name, t1)
        (c2, t2) = synth(nctx, t.body)
        term_vars = type_free_term_vars(t1)
        assert t.var_name not in term_vars
        r = (Conjunction(c1, implication_constraint(t.var_name, t1, c2)), t2)
        return r
    elif isinstance(t, Rec):
        nrctx: TypingContext = ctx.with_var(t.var_name, t.var_type)
        c1 = check(nrctx, t.var_value, t.var_type)
        (c2, t2) = synth(nrctx, t.body)
        c1 = implication_constraint(t.var_name, t.var_type, c1)
        c2 = implication_constraint(t.var_name, t.var_type, c2)
        return Conjunction(c1, c2), t2
    elif isinstance(t, Annotation):
        ty = fresh(ctx, t.type)
        c = check(ctx, t.expr, ty)
        return c, ty
    elif isinstance(t, TypeApplication):
        if not is_bare(t.type):
            # Type Application only works on bare types.
            raise TypeApplicationOnlyWorksOnBareTypesException(t, t.type)
        (c, tabs) = synth(ctx, t.body)
        assert isinstance(tabs, TypePolymorphism)  # TODO: Check this
        ty = fresh(ctx, t.type)
        s = type_substitution(tabs.body, tabs.name, ty)
        k = ctx.kind_of(ty)
        if isinstance(ty, RefinedType) and isinstance(ty.refinement, LiquidHornApplication):
            ty = ty.type
            k = ctx.kind_of(ty)
        if k is None or not is_compatible(k, tabs.kind):
            raise WrongKindInTypeApplication(t, expected=tabs.kind, actual=k)
        return (c, s)
    elif isinstance(t, Hole):
        name_a = Name("a", fresh_counter.fresh())
        return ctrue, TypePolymorphism(name_a, StarKind(), TypeVar(name_a))  # TODO poly: check kind
    else:
        logger.log("SYNTH_TYPE", ("Unhandled:", t))
        logger.log("SYNTH_TYPE", ("Unhandled:", type(t)))
        assert False, f"Unhandled term {t} in synth. Type: {type(t)}"


def check(ctx: TypingContext, t: Term, ty: Type) -> Constraint:
    try:
        assert wellformed(ctx, ty)
    except AssertionError:
        raise TypeNotWellformed(ty)

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
                raise CouldNotGenerateConstraintException("If condition not boolean")
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
                raise WrongKindException(found=var_kind, expected=var_kind, t=t, ty=ty)
            itype = substitute_vartype(var_body, TypeVar(name), var_name)
            return check(ctx.with_typevar(name, var_kind), body, itype)
        case _:
            (c, s) = synth(ctx, t)
            cp = sub(ctx, s, ty)

            if cp == LiquidConstraint(LiquidLiteralBool(False)):
                raise FailedSubtypingException(ctx, t, s, ty)
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
    except CouldNotGenerateConstraintException:
        return False
    except FailedConstraintException:
        return False
    except TypeNotWellformed:
        return False
