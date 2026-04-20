from __future__ import annotations

from aeon.core.instantiation import type_substitution
from aeon.core.terms import Annotation, Hole, Term, TypeApplication
from aeon.core.types import TypePolymorphism
from aeon.synthesis.modules.tdsyn.helpers import _collect_concrete_types
from aeon.synthesis.tactics.holes import collect_hole_judgments, replace_focal_hole
from aeon.synthesis.tactics.state import TacticState
from aeon.typechecking.typeinfer import is_compatible
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name, fresh_counter

_loc = SynthesizedLocation("tactics")


def tactic_inst(state: TacticState, hole_name: Name) -> TacticState | None:
    """``inst``: instantiate a ``forall`` goal with a concrete type from context (or built-ins).

    Replaces ``?h : forall a:k. B`` with ``(?i : forall a:k. B)[τ]``, where ``τ`` is the first
    well-kinded candidate from ``_collect_concrete_types``. If the hole's expected type is the
    synthesizer root goal, ``state.goal`` is updated to ``B[a := τ]``.
    """
    holes = collect_hole_judgments(state.ctx, state.term, state.goal, refined_types=True)
    if hole_name not in holes:
        return None
    goal_ty, hole_ctx = holes[hole_name]

    match goal_ty:
        case TypePolymorphism(pname, kind, pbody):
            pass
        case _:
            return None

    for tau in _collect_concrete_types(hole_ctx):
        try:
            tau_kind = hole_ctx.kind_of(tau)
        except (AssertionError, Exception):
            continue
        if not is_compatible(tau_kind, kind):
            continue
        inst_ty = type_substitution(pbody, pname, tau)
        hn = Name("_ti", fresh_counter.fresh())
        inner: Term = Annotation(Hole(hn, loc=_loc), goal_ty, loc=_loc)
        wrapped = TypeApplication(inner, tau, loc=_loc)
        new_term = replace_focal_hole(state.term, hole_name, wrapped)
        new_goal = inst_ty if goal_ty == state.goal else state.goal
        return TacticState(state.ctx, new_term, new_goal)

    return None
