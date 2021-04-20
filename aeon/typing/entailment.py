from aeon.core.substitutions import substitution, substitution_in_liquid
from typing import Tuple
from aeon.core.types import (
    AbstractionType,
    BaseType,
    RefinedType,
    Type,
    TypeVar,
    extract_parts,
)
from aeon.typing.context import EmptyContext, TypeBinder, TypingContext, VariableBinder
from aeon.core.liquid import LiquidTerm, LiquidLiteralBool, LiquidVar
from aeon.verification.vcs import Constraint, Implication

# from aeon.verification.smt import smt_valid
from aeon.verification.horn import solve


def entailment(ctx: TypingContext, c: Constraint):
    if isinstance(ctx, EmptyContext):
        return solve(c)
        # return smt_valid(c)
    elif isinstance(ctx, VariableBinder):
        if isinstance(ctx.type, AbstractionType):
            return entailment(ctx.prev, c)
        else:
            (name, base, cond) = extract_parts(ctx.type)
            ncond = substitution_in_liquid(cond, LiquidVar(ctx.name), name)
            return entailment(ctx.prev, Implication(ctx.name, base, ncond, c))
    elif isinstance(ctx, TypeBinder):
        return entailment(ctx.prev, c)  # TODO
    else:
        assert False
