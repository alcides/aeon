from __future__ import annotations

from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidVar
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import AbstractionType, BaseKind, TypeConstructor
from aeon.core.types import BaseType
from aeon.core.types import extract_parts
from aeon.core.types import Kind
from aeon.core.types import RefinedType
from aeon.core.types import StarKind
from aeon.core.types import t_bool
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.typechecking.context import TypeBinder, TypingContext, UninterpretedFunctionBinder
from aeon.typechecking.context import VariableBinder
from aeon.typechecking.liquid import type_infer_liquid
from aeon.verification.smt import smt_valid
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import Implication
from aeon.verification.vcs import LiquidConstraint


def wellformed(ctx: TypingContext, t: Type, k: Kind = StarKind()) -> bool:
    wf_norefinement = isinstance(t, BaseType)
    wf_base = (
        isinstance(t, RefinedType)
        and isinstance(t.type, BaseType)
        and wellformed(ctx, t.type, k)
        and type_infer_liquid(ctx.with_var(t.name, t.type), t.refinement) == t_bool
    )
    wf_fun = (
        isinstance(t, AbstractionType)
        and k == StarKind()
        and wellformed(ctx, t.var_type)
        and wellformed(ctx.with_var(t.var_name, t.var_type), t.type)
    )
    wf_kind = k == StarKind() and wellformed(ctx, t, BaseKind())

    wf_var_base = (
        isinstance(t, RefinedType)
        and isinstance(t.type, TypeVar)
        and k == BaseKind()
        and (t.type.name, BaseKind()) in ctx.typevars()
        and type_infer_liquid(ctx.with_var(t.name, t.type), t.refinement) == t_bool
    )

    wf_var = isinstance(t, TypeVar) and (t.name in [v[0] for v in ctx.typevars()])
    wf_var2 = (
        isinstance(t, RefinedType)
        and isinstance(t.type, TypeVar)
        and (t.refinement == LiquidLiteralBool(True))
        and (t.type.name, k) in ctx.typevars()
    )

    wf_data = isinstance(t, TypeConstructor) and all(wellformed(ctx, ta) for ta in t.args)
    wf_data2 = (
        isinstance(t, RefinedType)
        and isinstance(t.type, TypeConstructor)
        and all(wellformed(ctx, ta) for ta in t.type.args)
        and type_infer_liquid(ctx.with_var(t.name, t.type), t.refinement) == t_bool
    )

    wf_all = (
        isinstance(t, TypePolymorphism) and k == StarKind() and wellformed(ctx.with_typevar(t.name, t.kind), t.body)
    )
    return (
        wf_norefinement
        or wf_base
        or wf_fun
        or wf_kind
        or wf_var_base
        or wf_var
        or wf_var2
        or wf_all
        or wf_data
        or wf_data2
    )


def inhabited(ctx: TypingContext, ty: Type) -> bool:
    """y > 3.

    |-
    {x:Int | x > y}

    forall y > 3, exists x, x > 0
    """

    def entailment_like(ctx: TypingContext, c: Constraint):
        for entry in reversed(ctx.entries):
            match entry:
                case TypeBinder(name=_, kind=_):
                    pass
                case UninterpretedFunctionBinder(name=_, type=_):
                    pass
                case VariableBinder(name=_, type=TypePolymorphism(name=_, kind=_, body=_)):
                    pass
                case VariableBinder(name=_, type=AbstractionType(var_name=_, var_type=_, type=_)):
                    pass
                case VariableBinder(name=_, type=TypeVar(name=_)):
                    pass
                case VariableBinder(name=name, type=ty):
                    (ref_name, base, cond) = extract_parts(ty)
                    if isinstance(base, BaseType):
                        ncond = substitution_in_liquid(cond, LiquidVar(name), ref_name)
                        c = Implication(name, base, ncond, c)
                case _:
                    assert False
        return c

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
