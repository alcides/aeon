"""Modular Synquid-style hooks for synthesis (incremental decomposition).

These functions expose the same decomposition logic used by the Synquid
enumerator so other backends or tests can query subgoals without running the
full search. For a **whole** candidate at the hole, use ``check_hole_term``,
which is the same ``check_type`` path used elsewhere (not a separate partial
liquid calculus). Full program checking still substitutes the hole into the
surrounding definition in the synthesis driver.
"""

from __future__ import annotations

from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.synthesis.modules.synquid.decompose import synquid_application_arg_types, uncurry
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type

__all__ = ["application_subgoal_types", "check_hole_term", "uncurry"]


def application_subgoal_types(callee_type: Type, result_goal: Type) -> list[Type] | None:
    """Return per-argument synthesis goals for ``callee_type`` if its result matches ``result_goal``."""
    return synquid_application_arg_types(callee_type, result_goal)


def check_hole_term(ctx: TypingContext, term: Term, goal: Type) -> bool:
    """Return whether ``term`` has type ``goal`` in typing context ``ctx`` (``check_type``)."""
    return check_type(ctx, term, goal)
