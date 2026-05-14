"""Wrapper around aeon's subtyping check.

The SubType auxiliary of Eq. (1) of the paper produces a constraint over
positions: `i.type.t = j.type.t ∧ i.type.ref ⊨ j.type.ref`. Here we discharge
that constraint by reusing aeon's existing verifier (`aeon.verification.sub`)
which already encodes the same logic for the core type system.
"""

from __future__ import annotations


from aeon.core.types import Type
from aeon.typechecking.context import TypingContext
from aeon.verification.horn import solve
from aeon.verification.sub import sub


def is_subtype(ctx: TypingContext, t1: Type, t2: Type) -> bool:
    """Return True iff `t1 <: t2` under `ctx`."""
    try:
        constraint = sub(ctx, t1, t2)
        return solve(constraint, typing_ctx=ctx)
    except Exception:
        return False


_subtype_cache: dict[tuple[int, str, str], bool] = {}


def is_subtype_cached(ctx: TypingContext, t1: Type, t2: Type) -> bool:
    """Memoized variant. The cache key uses repr() rather than identity so
    structurally identical types share results across iterations."""
    key = (id(ctx), repr(t1), repr(t2))
    if key in _subtype_cache:
        return _subtype_cache[key]
    result = is_subtype(ctx, t1, t2)
    _subtype_cache[key] = result
    return result
