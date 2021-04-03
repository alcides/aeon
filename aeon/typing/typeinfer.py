from aeon.typing.entailment import entailment
from aeon.core.substitutions import liquefy, substitute_vartype, substitution_in_type
from aeon.verification.vcs import (
    Conjunction,
    Constraint,
    LiquidConstraint,
    variables_in,
)
from typing import Tuple

from aeon.core.liquid import (
    LiquidApp,
    LiquidLiteralBool,
    LiquidLiteralInt,
    LiquidVar,
)
from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    If,
    Let,
    Literal,
    Rec,
    Term,
    Var,
)
from aeon.core.types import (
    AbstractionType,
    BaseType,
    RefinedType,
    Type,
    TypeVar,
    extract_parts,
    t_bool,
    t_int,
    t_string,
    t_float,
    top,
    bottom,
    type_free_term_vars,
)
from aeon.typing.context import TypingContext
from aeon.core.liquid_ops import ops
from aeon.verification.sub import ensure_refined, implication_constraint, sub
from aeon.verification.horn import fresh

ctrue = LiquidConstraint(LiquidLiteralBool(True))


class CouldNotGenerateConstraintException(Exception):
    pass


def argument_is_typevar(ty: Type):
    return (
        isinstance(ty, TypeVar)
        or isinstance(ty, RefinedType)
        and isinstance(ty.type, TypeVar)
    )


def prim_litbool(t: bool) -> RefinedType:
    if t:
        return RefinedType("v", t_bool, LiquidVar("v"))
    else:
        return RefinedType("v", t_bool, LiquidApp("!", [LiquidVar("v")]))


def prim_litint(t: int) -> RefinedType:
    return RefinedType(
        "v", t_int, LiquidApp("==", [LiquidVar("v"), LiquidLiteralInt(t)])
    )


def prim_op(t: str) -> Type:
    i1 = TypeVar("_op_1")
    i2 = TypeVar("_op_1")
    o = TypeVar("_op_1")

    if t in ["==", "!=", "<", ">", "<=", ">=", "&&", "||"]:
        o = t_bool
    if t in ["&&", "||"]:
        i1 = t_bool
        i2 = t_bool

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
def synth(ctx: TypingContext, t: Term) -> Tuple[Constraint, Type]:
    if isinstance(t, Literal) and t.type == t_bool:
        return (ctrue, prim_litbool(t.value))
    elif isinstance(t, Literal) and t.type == t_int:
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
                "Variable {} not in context", t.name
            )
        return (ctrue, ty)
    elif isinstance(t, Application):
        (c, ty) = synth(ctx, t.fun)
        if isinstance(ty, AbstractionType):

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
            r = (Conjunction(c, cp), t_subs)
            assert ty.var_name not in list(variables_in(r))
            return r
        else:
            raise CouldNotGenerateConstraintException()
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

        print(
            "\tLetRec",
            list(variables_in(c1)),
            ", ",
            list(variables_in(c2)),
            " ... ",
            t.var_name,
            " >=>",
            ctx,
            "??",
            c1,
            "??",
            c2,
        )

        return (Conjunction(c1, c2), t2)
    elif isinstance(t, Annotation):
        ty = fresh(ctx, t.type)
        c = check(ctx, t.expr, ty)
        return (c, ty)
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
        if not check_type(ctx, t.cond, t_bool):
            raise CouldNotGenerateConstraintException("If condition not boolean")
        c0 = check(ctx, t.cond, t_bool)
        c1 = implication_constraint(
            y, RefinedType("branch_", t_int, liq_cond), check(ctx, t.then, ty)
        )
        c2 = implication_constraint(
            y,
            RefinedType("branch_", t_int, LiquidApp("!", [liq_cond])),
            check(ctx, t.otherwise, ty),
        )
        return Conjunction(c0, Conjunction(c1, c2))
    else:
        (c, s) = synth(ctx, t)
        cp = sub(s, ty)
        return Conjunction(c, cp)


def check_type(ctx: TypingContext, t: Term, ty: Type) -> bool:
    # print(ctx, "|-", t, "<:", ty)
    try:
        constraint = check(ctx, t, ty)
    except CouldNotGenerateConstraintException as e:
        print("OOPs", e)
        return False

    # print("Checking {} <: {} leads to {}".format(t, ty, constraint))
    return entailment(ctx, constraint)
