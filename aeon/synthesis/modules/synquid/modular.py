"""Modular Synquid-style hooks for synthesis (incremental decomposition).

These functions expose the same decomposition logic used by the Synquid
enumerator so other backends or tests can query subgoals without running the
full search. Full round-trip liquid checking remains in ``typeinfer`` /
``entailment``; here we only split types along function spines.
"""

from __future__ import annotations

from aeon.core.types import Type
from aeon.synthesis.modules.synquid.decompose import synquid_application_arg_types, uncurry

__all__ = ["application_subgoal_types", "uncurry"]


def application_subgoal_types(callee_type: Type, result_goal: Type) -> list[Type] | None:
    """Return per-argument synthesis goals for ``callee_type`` if its result matches ``result_goal``."""
    return synquid_application_arg_types(callee_type, result_goal)
