from typing import Tuple
from aeon.core.types import BaseType, RefinedType, Type, extract_parts
from aeon.typing.context import EmptyContext, TypingContext, VariableBinder
from aeon.core.liquid import LiquidTerm, LiquidLiteralBool
from aeon.verification.vcs import Constraint, Implication
from aeon.verification.smt import smt_valid


def entailment(ctx: TypingContext, c: Constraint):
    if isinstance(ctx, EmptyContext):
        return smt_valid(c)
    elif isinstance(ctx, VariableBinder):
        (name, base, cond) = extract_parts(ctx.type)
        return entailment(ctx.prev, Implication(ctx.name, base, cond, c))
    else:
        assert False
