from aeon.core.liquid import LiquidLiteralBool, LiquidVar
from aeon.core.substitutions import substitution_in_liquid
from aeon.verification.smt import smt_valid
from aeon.verification.vcs import Constraint, Implication, LiquidConstraint
from aeon.typing.liquid import type_infer_liquid
from aeon.core.types import (
    Kind,
    StarKind,
    Type,
    BaseType,
    TypeVar,
    AbstractionType,
    RefinedType,
    extract_parts,
    t_bool,
)
from aeon.typing.context import EmptyContext, TypingContext, VariableBinder
from aeon.verification.sub import ensure_refined, implication_constraint


def wellformed(ctx: TypingContext, t: Type, k: Kind = StarKind()) -> bool:
    wf_norefinement = isinstance(t, BaseType)
    wf_var = isinstance(t, TypeVar) and ctx.contains_typevar(t.name, k)
    wf_base = (
        isinstance(t, RefinedType)
        and wellformed(ctx, t.type, k)
        and type_infer_liquid(ctx.with_var(t.name, t.type), t.refinement) == t_bool
    )
    wf_fun = (
        isinstance(t, AbstractionType)
        and k == StarKind()
        and wellformed(ctx, t.var_type)
        and wellformed(ctx.with_var(t.var_name, t.var_type), t.type)
    )
    return wf_simplecases or wf_base or wf_fun


def inhabited(ctx: TypingContext, ty: Type) -> bool:
    """
    y > 3
    |-
    {x:Int | x > y}

    forall y > 3, exists x, x > 0
    """

    def entailment_like(ctx: TypingContext, c: Constraint):
        if isinstance(ctx, EmptyContext):
            return c
        elif isinstance(ctx, VariableBinder):
            (name, base, cond) = extract_parts(ctx.type)
            ncond = substitution_in_liquid(cond, LiquidVar(ctx.name), name)
            return entailment_like(ctx.prev, Implication(ctx.name, base, ncond, c))
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


"""
Notas:

forall k:int, k > 3
exists x:int, x > k && x < 2

exists k, k > 3 --> forall x:int, True -> x > k && x < 2
"""
