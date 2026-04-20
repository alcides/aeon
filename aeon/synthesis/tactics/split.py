from __future__ import annotations

from aeon.core.liquid import LiquidApp
from aeon.core.types import RefinedType, Type
from aeon.synthesis.tactics.holes import collect_hole_judgments, replace_hole_expected_annotation
from aeon.synthesis.tactics.state import TacticState
from aeon.utils.name import Name

_and = Name("&&", 0)


def tactic_split(state: TacticState, hole_name: Name) -> TacticState | None:
    """``split``: peel a top-level liquid conjunction in the hole's refinement.

    If the hole expects ``{x:T | P && Q}``, rewrite the annotation to ``{x:T | P}``.
    The synthesizer's root ``goal`` type is unchanged, so final ``validate`` still
    requires the full conjunction once the term is complete.
    """
    holes = collect_hole_judgments(state.ctx, state.term, state.goal, refined_types=True)
    if hole_name not in holes:
        return None
    goal_ty: Type
    goal_ty, _hole_ctx = holes[hole_name]

    match goal_ty:
        case RefinedType(n, base, LiquidApp(fun, [p, _]), loc=rloc) if fun == _and:
            new_ty = RefinedType(n, base, p, loc=rloc)
            new_term = replace_hole_expected_annotation(state.term, hole_name, new_ty)
            return TacticState(state.ctx, new_term, state.goal)
        case _:
            return None
