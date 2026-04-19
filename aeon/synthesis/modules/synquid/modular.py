"""Modular Synquid-style hooks for synthesis (incremental decomposition).

These functions expose the same decomposition logic used by the Synquid
enumerator so other backends or tests can query subgoals without running the
full search. For a **whole** candidate at the hole, ``check_hole_term`` mirrors
``check_type``. For the **verification condition** as a separate object (so
you can inspect constraints, tune **Q**, or diagnose failures), use
``build_modular_vc`` / ``ModularVC`` from ``aeon.typechecking.partial_vc``
(also re-exported here). Full program checking still substitutes the hole into
the surrounding definition in the synthesis driver.
"""

from __future__ import annotations

from aeon.core.liquid import LiquidTerm
from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.synthesis.modules.synquid.decompose import synquid_application_arg_types, uncurry
from aeon.typechecking.context import TypingContext
from aeon.typechecking.partial_vc import ModularVC, build_modular_vc
from aeon.typechecking.qualifiers import extract_qualifier_atoms
from aeon.typechecking.typeinfer import check_type

__all__ = [
    "ModularVC",
    "application_subgoal_types",
    "build_modular_vc",
    "check_hole_term",
    "qualifier_atoms",
    "uncurry",
]


def application_subgoal_types(callee_type: Type, result_goal: Type) -> list[Type] | None:
    """Return per-argument synthesis goals for ``callee_type`` if its result matches ``result_goal``."""
    return synquid_application_arg_types(callee_type, result_goal)


def check_hole_term(ctx: TypingContext, term: Term, goal: Type) -> bool:
    """Return whether ``term`` has type ``goal`` in typing context ``ctx`` (``check_type``)."""
    return check_type(ctx, term, goal)


def qualifier_atoms(
    ctx: TypingContext,
    *,
    goal_type: Type | None = None,
    term: Term | None = None,
    max_atoms: int = 512,
) -> frozenset[LiquidTerm]:
    """Finite qualifier set **Q** (same as Horn / Synquid guard extraction)."""
    return extract_qualifier_atoms(ctx, goal_type, term, max_atoms=max_atoms)
