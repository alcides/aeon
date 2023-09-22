from __future__ import annotations

from aeon.core.liquid import LiquidVar
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import AbstractionType
from aeon.core.types import BaseType
from aeon.core.types import extract_parts
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.typechecking.context import EmptyContext
from aeon.typechecking.context import TypeBinder
from aeon.typechecking.context import TypingContext
from aeon.typechecking.context import UninterpretedBinder
from aeon.typechecking.context import VariableBinder
from aeon.verification.helpers import show_constraint
from aeon.verification.horn import solve
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import Implication
from aeon.verification.vcs import UninterpretedFunctionDeclaration


def entailment(ctx: TypingContext, c: Constraint):
    if isinstance(ctx, EmptyContext):
        r = solve(c)
        return r
    elif isinstance(ctx, VariableBinder):
        if isinstance(ctx.type, AbstractionType):
            return entailment(ctx.prev, c)
        if isinstance(ctx.type, TypePolymorphism):
            return entailment(ctx.prev, c)  # TODO: check that this is not relevant
        else:
            ty: Type = ctx.type
            (name, base, cond) = extract_parts(ty)
            if isinstance(base, BaseType):
                ncond = substitution_in_liquid(cond, LiquidVar(ctx.name), name)
                return entailment(
                    ctx.prev,
                    Implication(ctx.name, base, ncond, c),
                )
            elif isinstance(ctx.type, TypeVar):
                assert False  # TypeVars are being replaced by Int
            else:
                assert False

    elif isinstance(ctx, TypeBinder):
        return entailment(
            ctx.prev,
            c,
        )  # TODO: Consider passing as a concrete placeholder type for SMT
    elif isinstance(ctx, UninterpretedBinder):
        return entailment(
            ctx.prev,
            UninterpretedFunctionDeclaration(ctx.name, ctx.type, c),
        )
    else:
        assert False
