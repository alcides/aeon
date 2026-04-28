from __future__ import annotations

from aeon.core.terms import Annotation, Hole, If, Term, Var
from aeon.core.types import Type, t_bool
from aeon.synthesis.grammar.utils import SYNTHESIS_EXCLUDED_NAMES
from aeon.synthesis.tactics.holes import collect_hole_judgments, replace_hole
from aeon.synthesis.tactics.state import TacticState
from aeon.synthesis.tactics.subtyping import fits
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name, fresh_counter

_loc = SynthesizedLocation("tactics")


def tactic_by_cases(state: TacticState, hole_name: Name) -> TacticState | None:
    """``by_cases``: split on the first Boolean hypothesis ``b`` with ``bty <: Bool``.

    Replaces the goal hole with ``if b then ?_then else ?_else``, reusing the same
    goal type in both branches (Liquid ``If`` typing discharges branch VCs).
    """
    holes = collect_hole_judgments(state.ctx, state.term, state.goal, refined_types=True)
    if hole_name not in holes:
        return None
    goal_ty: Type
    goal_ty, hole_ctx = holes[hole_name]

    for b, bty in hole_ctx.concrete_vars():
        if b.name in SYNTHESIS_EXCLUDED_NAMES:
            continue
        if not fits(hole_ctx, bty, t_bool):
            continue
        hthen = Name("_then", fresh_counter.fresh())
        helse = Name("_else", fresh_counter.fresh())
        br_then: Term = Annotation(Hole(hthen), goal_ty, loc=_loc)
        br_else: Term = Annotation(Hole(helse), goal_ty, loc=_loc)
        ite = If(Var(b, _loc), br_then, br_else, loc=_loc)
        return TacticState(state.ctx, replace_hole(state.term, hole_name, ite), state.goal)

    return None
