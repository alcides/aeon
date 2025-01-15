from __future__ import annotations

from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidVar
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import AbstractionType, BaseKind, Bottom, Top
from aeon.core.types import BaseType
from aeon.core.types import extract_parts
from aeon.core.types import Kind
from aeon.core.types import RefinedType
from aeon.core.types import StarKind
from aeon.core.types import t_bool
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.typechecking.context import EmptyContext
from aeon.typechecking.context import TypingContext
from aeon.typechecking.context import VariableBinder
from aeon.typechecking.liquid import typecheck_liquid
from aeon.verification.smt import smt_valid
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import Implication
from aeon.verification.vcs import LiquidConstraint


def wf_inner(ctx: TypingContext, t: Type, k: Kind = StarKind()) -> bool:
    match t:
        case BaseType(_) | Top() | Bottom():
            return True  # wf_no_refinement
        case RefinedType(name, BaseType(_) as ty, refinement):
            inferred_type = typecheck_liquid(ctx.with_var(name, ty),
                                             refinement)
            return inferred_type == t_bool
        case TypeVar(tvname):
            return tvname in [v[0] for v in ctx.typevars()]
        case RefinedType(name, TypeVar(tvname), LiquidLiteralBool(True)):
            return (tvname, k) in ctx.typevars()
        case RefinedType(name, TypeVar(tvname) as ty, refinement):
            return (k == BaseKind() and (tvname, BaseKind()) in ctx.typevars()
                    and typecheck_liquid(ctx.with_var(name, ty),
                                         refinement) == t_bool)
        case AbstractionType(aname, atype, rtype):
            return k == StarKind() and wellformed(ctx, atype) and wellformed(
                ctx.with_var(aname, atype), rtype)
        case TypePolymorphism(name, kind, body):
            return k == StarKind() and wellformed(ctx.with_typevar(name, kind),
                                                  body)
        case _:
            return False


def wellformed(ctx: TypingContext, t: Type, k: Kind = StarKind()) -> bool:
    match k:
        case StarKind():
            return wf_inner(ctx, t, StarKind()) or wf_inner(ctx, t, BaseKind())
        case _:
            return wf_inner(ctx, t, BaseKind())


def inhabited(ctx: TypingContext, ty: Type) -> bool:
    """y > 3.

    |-
    {x:Int | x > y}

    forall y > 3, exists x, x > 0
    """

    def entailment_like(ctx: TypingContext, c: Constraint):
        if isinstance(ctx, EmptyContext):
            return c
        elif isinstance(ctx, VariableBinder):
            (name, base, cond) = extract_parts(ctx.type)
            assert isinstance(base, BaseType)  # TODO: check if make sense
            ncond = substitution_in_liquid(cond, LiquidVar(ctx.name), name)
            return entailment_like(ctx.prev,
                                   Implication(ctx.name, base, ncond, c))
        else:
            assert False

    try:
        (name, base, refinement) = extract_parts(ty)
        constraint = LiquidConstraint(refinement)
        wrapper = Implication(
            "__internal__",
            t_bool,
            LiquidLiteralBool(True),
            entailment_like(ctx, constraint),
        )
        r = smt_valid(wrapper, foralls=[(name, base)])
        return r
    except ZeroDivisionError:
        return False
