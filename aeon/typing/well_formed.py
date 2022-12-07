from __future__ import annotations

from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidVar
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import AbstractionType
from aeon.core.types import BaseKind
from aeon.core.types import BaseType
from aeon.core.types import extract_parts
from aeon.core.types import Kind
from aeon.core.types import RefinedType
from aeon.core.types import StarKind
from aeon.core.types import t_bool
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.typing.context import EmptyContext
from aeon.typing.context import TypingContext
from aeon.typing.context import VariableBinder
from aeon.typing.liquid import type_infer_liquid
from aeon.verification.smt import smt_valid
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import Implication
from aeon.verification.vcs import LiquidConstraint


def wellformed(ctx: TypingContext, t: Type, k: Kind = StarKind()) -> bool:
    # TODO: debug
    # if isinstance(t, TypeVar):
    #    print("d", ctx, t, k, ctx.typevars(), (t.name, BaseKind()))
    wf_norefinement = isinstance(t, BaseType)
    wf_var = isinstance(
        t, TypeVar) and (k == StarKind() and ((t.name, k) in ctx.typevars()) or
                         (t.name in [v[0] for v in ctx.typevars()]))
    wf_base = (isinstance(t, RefinedType)
               and wellformed(ctx, t.type, k) and type_infer_liquid(
                   ctx.with_var(t.name, t.type), t.refinement) == t_bool)
    wf_fun = (isinstance(t, AbstractionType) and k == StarKind()
              and wellformed(ctx, t.var_type)
              and wellformed(ctx.with_var(t.var_name, t.var_type), t.type))
    wf_all = (isinstance(t, TypePolymorphism) and k == StarKind()
              and wellformed(ctx.with_typevar(t.name, t.kind), t.body))
    return wf_norefinement or wf_var or wf_base or wf_fun or wf_all


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
