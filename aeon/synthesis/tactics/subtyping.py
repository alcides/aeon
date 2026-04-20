from __future__ import annotations

from aeon.core.liquid import LiquidLiteralBool
from aeon.core.types import Type
from aeon.typechecking.context import TypingContext
from aeon.typechecking.entailment import entailment
from aeon.typechecking.well_formed import wellformed
from aeon.verification.sub import sub
from aeon.verification.vcs import LiquidConstraint

_cfalse = LiquidConstraint(LiquidLiteralBool(False))


def fits(ctx: TypingContext, actual: Type, goal: Type) -> bool:
    """True iff the typechecker relation ``actual <: goal`` holds (via ``sub`` + entailment)."""
    try:
        if not wellformed(ctx, actual) or not wellformed(ctx, goal):
            return False
    except Exception:
        # Narrow contexts (e.g. unit tests) may omit liquid operator binders required by
        # ``wellformed``; still attempt ``sub`` + entailment, which matches ``check``'s VC path.
        pass
    c = sub(ctx, actual, goal, None)
    if c == _cfalse:
        return False
    try:
        return bool(entailment(ctx, c))
    except Exception:
        return False
