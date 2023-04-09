from __future__ import annotations

from aeon.core.instantiation import type_substition
from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidVar
from aeon.core.liquid_ops import ops
from aeon.core.substitutions import liquefy
from aeon.core.substitutions import substitute_vartype
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
from aeon.core.types import AbstractionType
from aeon.core.types import args_size_of_type
from aeon.core.types import BaseKind
from aeon.core.types import BaseType
from aeon.core.types import bottom
from aeon.core.types import extract_parts
from aeon.core.types import RefinedType
from aeon.core.types import t_bool
from aeon.core.types import t_int
from aeon.core.types import t_unit
from aeon.core.types import Type
from aeon.core.types import type_free_term_vars
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.typechecking.context import TypingContext
from aeon.typechecking.entailment import entailment
from aeon.verification.horn import fresh
from aeon.verification.sub import ensure_refined
from aeon.verification.sub import implication_constraint
from aeon.verification.sub import sub
from aeon.verification.vcs import Conjunction
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import LiquidConstraint

ctrue = LiquidConstraint(LiquidLiteralBool(True))


class CouldNotGenerateConstraintException(Exception):
    pass


def argument_is_typevar(ty: Type):
    return isinstance(ty, TypeVar) or isinstance(ty, RefinedType) and isinstance(ty.type, TypeVar)


def prim_litbool(t: bool) -> RefinedType:
    if t:
        return RefinedType("v", t_bool, LiquidVar("v"))
    else:
        return RefinedType("v", t_bool, LiquidApp("!", [LiquidVar("v")]))


def prim_litint(t: int) -> RefinedType:
    return RefinedType(
        "v",
        t_int,
        LiquidApp("==", [LiquidVar("v"), LiquidLiteralInt(t)]),
    )


def prim_op(t: str) -> Type:
    # TODO add suport to floats
    i1: Type
    i2: Type
    o: Type
    if t in ["+", "*", "-", "/", "%"]:
        i1 = i2 = t_int
        o = t_int
    elif t in ["<", ">", "<=", ">="]:
        i1 = i2 = t_int
        o = t_bool
    elif t in ["&&", "||"]:
        i1 = i2 = o = t_bool
    elif t in ["==", "!="]:
        i1 = TypeVar("_op_1")
        i2 = TypeVar("_op_2")
        o = t_bool
    else:
        print(t)
        assert False

    return AbstractionType(
        "x",
        i1,
        AbstractionType(
            "y",
            i2,
            RefinedType(
                "z",
                o,
                LiquidApp(
                    "==",
                    [LiquidVar("z"), LiquidApp(t, [LiquidVar("x"), LiquidVar("y")])],
                ),
            ),
        ),
    )


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
    elif isinstance(t, Literal):
        return (ctrue, t.type)
    elif isinstance(t, Var):
        if t.name in ops:
            return (ctrue, prim_op(t.name))
        ty = ctx.type_of(t.name)
        if isinstance(ty, BaseType) or isinstance(ty, RefinedType):
            ty = ensure_refined(ty)
            assert ty.name != t.name
            # TODO if the names are equal , we must replace it for another variable
            # Self
            ty = RefinedType(
                ty.name,
                ty.type,
                LiquidApp(
                    "&&",
                    [
                        ty.refinement,
                        LiquidApp("==", [LiquidVar(ty.name), LiquidVar(t.name)]),
                    ],
                ),
            )
        if not ty:
            raise CouldNotGenerateConstraintException(
                f"Variable {t.name} not in context",
            )
        return (ctrue, ty)
    elif isinstance(t, Application):
        (c, ty) = synth(ctx, t.fun)
        if isinstance(ty, AbstractionType):
            # This is the solution to handle polymorphic "==" in refinements.
            if argument_is_typevar(ty.var_type):
                (_, b, _) = extract_parts(ty.var_type)
                assert isinstance(b, TypeVar)
                (cp, at) = synth(ctx, t.arg)
                if isinstance(at, RefinedType):
                    at = at.type  # This is a hack before inference
                return_type = substitute_vartype(ty.type, at, b.name)
            else:
                cp = check(ctx, t.arg, ty.var_type)
                return_type = ty.type
            t_subs = substitution_in_type(return_type, t.arg, ty.var_name)
            c0 = Conjunction(c, cp)
            # vs: list[str] = list(variables_free_in(c0))
            return (c0, t_subs)
        else:
            raise CouldNotGenerateConstraintException(f"Application {t} is not a function.")
    elif isinstance(t, Let):
        (c1, t1) = synth(ctx, t.var_value)
        nctx: TypingContext = ctx.with_var(t.var_name, t1)
        (c2, t2) = synth(nctx, t.body)
        assert t.var_name not in type_free_term_vars(t2)
        r = (Conjunction(c1, implication_constraint(t.var_name, t1, c2)), t2)
        return r
    elif isinstance(t, Rec):
        nrctx: TypingContext = ctx.with_var(t.var_name, t.var_type)
        c1 = check(nrctx, t.var_value, t.var_type)
        (c2, t2) = synth(nrctx, t.body)

        c1 = implication_constraint(t.var_name, t.var_type, c1)
        c2 = implication_constraint(t.var_name, t.var_type, c2)
        return (Conjunction(c1, c2), t2)
    elif isinstance(t, Annotation):
        ty = fresh(ctx, t.type)
        c = check(ctx, t.expr, ty)
        return (c, ty)
    elif isinstance(t, TypeApplication):
        (c, tabs) = synth(ctx, t.body)
        assert isinstance(tabs, TypePolymorphism)  # TODO: Check this
        ty = fresh(ctx, t.type)
        s = type_substition(tabs.body, tabs.name, ty)
        return (c, s)
    elif isinstance(t, Hole):
        return (ctrue, bottom)

    print("Unhandled:", t)
    assert False


# patterm matching term
def check(ctx: TypingContext, t: Term, ty: Type) -> Constraint:
    if isinstance(t, Abstraction) and isinstance(ty, AbstractionType):
        ret = substitution_in_type(ty.type, Var(t.var_name), ty.var_name)
        c = check(ctx.with_var(t.var_name, ty.var_type), t.body, ret)
        return implication_constraint(t.var_name, ty.var_type, c)

    elif isinstance(t, Let):
        (c1, t1) = synth(ctx, t.var_value)
        nctx: TypingContext = ctx.with_var(t.var_name, t1)
        c2 = check(nctx, t.body, ty)
        return Conjunction(c1, implication_constraint(t.var_name, t1, c2))

    elif isinstance(t, Rec):
        t1 = fresh(ctx, t.var_type)
        nrctx: TypingContext = ctx.with_var(t.var_name, t1)
        c1 = check(nrctx, t.var_value, t.var_type)
        c2 = check(nrctx, t.body, ty)
        c1 = implication_constraint(t.var_name, t1, c1)
        c2 = implication_constraint(t.var_name, t1, c2)
        return Conjunction(c1, c2)
    elif isinstance(t, If):
        y = ctx.fresh_var()
        liq_cond = liquefy(t.cond)
        assert liq_cond is not None
        if not check_type(ctx, t.cond, t_bool):
            raise CouldNotGenerateConstraintException("If condition not boolean")
        c0 = check(ctx, t.cond, t_bool)
        c1 = implication_constraint(
            y,
            RefinedType("branch_", t_int, liq_cond),
            check(ctx, t.then, ty),
        )
        c2 = implication_constraint(
            y,
            RefinedType("branch_", t_int, LiquidApp("!", [liq_cond])),
            check(ctx, t.otherwise, ty),
        )
        return Conjunction(c0, Conjunction(c1, c2))
    elif isinstance(t, TypeAbstraction) and isinstance(ty, TypePolymorphism):
        ty_right = type_substition(ty, ty.name, TypeVar(t.name))
        assert isinstance(ty_right, TypePolymorphism)
        if ty_right.kind == BaseKind() and t.kind != ty_right.kind:
            return LiquidConstraint(LiquidLiteralBool(False))
        return check(ctx.with_typevar(t.name, t.kind), t.body, ty_right.body)
    else:
        (c, s) = synth(ctx, t)
        cp = sub(s, ty)
        return Conjunction(c, cp)


def check_type(ctx: TypingContext, t: Term, ty: Type) -> bool:
    # print(ctx, "|-", t, "<:", ty)
    try:
        constraint = check(ctx, t, ty)
    except CouldNotGenerateConstraintException as e:
        print("Type Error", e)
        return False

    # print("Checking {} <: {} leads to {}".format(t, ty, constraint))
    return entailment(ctx, constraint)


def is_subtype(ctx: TypingContext, subt: Type, supt: Type):
    if args_size_of_type(subt) != args_size_of_type(supt):
        return False
    if subt == supt:
        return True
    if isinstance(subt, RefinedType) and subt.type == supt:
        return True
    c = sub(subt, supt)
    if isinstance(c, LiquidLiteralBool):
        return c.value
    r = entailment(ctx, c)
    return r
