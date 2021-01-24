from aeon.typing.entailment import entailment
from aeon.core.substitutions import liquefy, substitution_in_type
from aeon.verification.vcs import Conjunction, Constraint, LiquidConstraint
from typing import Tuple

from aeon.core.liquid import (
    LiquidApp,
    LiquidLiteralBool,
    LiquidLiteralInt,
    LiquidVar,
)
from aeon.core.terms import Abstraction, Application, If, Let, Literal, Term, Var
from aeon.core.types import (
    AbstractionType,
    BaseType,
    RefinedType,
    Type,
    t_bool,
    t_int,
    top,
    bottom,
)
from aeon.typing.context import TypingContext
from aeon.core.liquid_ops import ops
from aeon.verification.sub import ensure_refined, implication_constraint, sub

ctrue = LiquidConstraint(LiquidLiteralBool(True))


class CouldNotGenerateConstraintException(Exception):
    pass


def prim_litbool(t: bool) -> RefinedType:
    if t:
        return RefinedType("v", t_bool, LiquidVar("v"))
    else:
        return RefinedType("v", t_bool, LiquidApp("!", [LiquidVar("v")]))


def prim_litint(t: int) -> RefinedType:
    return RefinedType(
        "v", t_int,
        LiquidApp("==", [LiquidVar("v"), LiquidLiteralInt(t)]))


def prim_op(t: str) -> Type:
    return AbstractionType(
        "x",
        top,
        AbstractionType(
            "y",
            top,
            RefinedType("z", bottom,
                        LiquidApp(
                            t, [LiquidVar("x"), LiquidVar("y")])),
        ),
    )


# patterm matching term
def synth(ctx: TypingContext, t: Term) -> Tuple[Constraint, Type]:
    if isinstance(t, Literal) and t.type == t_bool:
        return (ctrue, prim_litbool(t.value))
    elif isinstance(t, Literal) and t.type == t_int:
        return (ctrue, prim_litint(t.value))
    elif isinstance(t, Var):
        if t.name in ops:
            return (ctrue, prim_op(t.name))
        ty = ctx.type_of(t.name)
        if isinstance(ty, BaseType) or isinstance(ty, RefinedType):
            ty = ensure_refined(ty)
            # Self
            ty = RefinedType(
                ty.name,
                ty.type,
                LiquidApp(
                    "&&",
                    [
                        ty.refinement,
                        LiquidApp("==",
                                  [LiquidVar(ty.name),
                                   LiquidVar(t.name)]),
                    ],
                ),
            )
        if not ty:
            raise CouldNotGenerateConstraintException(
                "Variable {} not in context", t.name)
        return (ctrue, ty)
    elif isinstance(t, Application):
        (c, ty) = synth(ctx, t.fun)
        if isinstance(ty, AbstractionType):
            cp = check(ctx, t.arg, ty.var_type)
            t_subs = substitution_in_type(ty.type, Var(t.arg), ty.var_name)
            print("app", t, t_subs)
            return (Conjunction(c, cp), t_subs)
        else:
            raise CouldNotGenerateConstraintException()
    assert False


# patterm matching term
def check(ctx: TypingContext, t: Term, ty: Type) -> Constraint:
    if isinstance(t, Abstraction) and isinstance(ty, AbstractionType):
        ret = substitution_in_type(ty.type, Var(t.var_name), ty.var_name)
        c = check(ctx.with_var(t.var_name, ty.var_type), t.body, ret)
        c_ = implication_constraint(t.var_name, ty.var_type, c)
        return c_
    elif isinstance(t, Let):
        (c1, t1) = synth(ctx, t.var_value)
        nctx: TypingContext = ctx.with_var(t.var_name, t1)
        c2 = check(nctx, t.body, ty)
        return Conjunction(c1, implication_constraint(t.var_name, t1, c2))
    elif isinstance(t, If):
        y = ctx.fresh_var()
        liq_cond = liquefy(t.cond)
        print("Liq", liq_cond)
        # c0 = check(ctx, t.cond, t_bool) TODO!
        c1 = implication_constraint(y, RefinedType("branch_", t_int, liq_cond),
                                    check(ctx, t.then, ty))
        c2 = implication_constraint(
            y,
            RefinedType("branch_", t_int, LiquidApp("!", [liq_cond])),
            check(ctx, t.otherwise, ty),
        )
        return Conjunction(c1, c2)
    else:
        (c, s) = synth(ctx, t)
        cp = sub(s, ty)
        return Conjunction(c, cp)


def check_type(ctx, t: Term, ty: Type) -> bool:
    constraint = check(ctx, t, ty)
    return entailment(ctx, constraint)
