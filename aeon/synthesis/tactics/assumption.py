from __future__ import annotations

from aeon.core.terms import Var
from aeon.synthesis.grammar.utils import SYNTHESIS_EXCLUDED_NAMES
from aeon.synthesis.tactics.holes import collect_hole_judgments, replace_hole
from aeon.synthesis.tactics.state import TacticState
from aeon.synthesis.tactics.subtyping import fits
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name

_loc = SynthesizedLocation("tactics")


def tactic_assumption(state: TacticState, hole_name: Name) -> TacticState | None:
    """``assumption``: close the goal with a hypothesis of (approximately) the same type.

    Picks the first context variable ``x`` such that ``xty <: goal`` and ``goal <: xty``
    (bidirectional subtyping via ``fits``), matching the usual ``assumption`` / ``exact``
    story up to liquid definitional equivalence.
    """
    holes = collect_hole_judgments(state.ctx, state.term, state.goal, refined_types=True)
    if hole_name not in holes:
        return None
    goal_ty, hole_ctx = holes[hole_name]

    for x, xty in hole_ctx.concrete_vars():
        if x.name in SYNTHESIS_EXCLUDED_NAMES:
            continue
        if fits(hole_ctx, xty, goal_ty) and fits(hole_ctx, goal_ty, xty):
            return TacticState(state.ctx, replace_hole(state.term, hole_name, Var(x, _loc)), state.goal)

    return None
