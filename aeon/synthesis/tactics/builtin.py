from __future__ import annotations

from aeon.core.substitutions import substitution_in_type
from aeon.core.terms import Abstraction, Annotation, Application, Hole, Term, Var
from aeon.core.types import AbstractionType, Type
from aeon.synthesis.grammar.utils import SYNTHESIS_EXCLUDED_NAMES
from aeon.synthesis.tactics.holes import collect_hole_judgments, replace_hole
from aeon.synthesis.tactics.state import TacticState
from aeon.synthesis.tactics.subtyping import fits
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name, fresh_counter

_loc = SynthesizedLocation("tactics")


def _split_arrow_spine(ty: Type) -> tuple[list[Type], Type]:
    params: list[Type] = []
    t = ty
    while isinstance(t, AbstractionType):
        params.append(t.var_type)
        t = t.type
    return params, t


def tactic_apply_question(state: TacticState, hole_name: Name) -> TacticState | None:
    """``apply?``: use the first hypothesis ``x`` (in context order) with ``ctx_ty(x) <: goal``."""
    holes = collect_hole_judgments(state.ctx, state.term, state.goal, refined_types=True)
    if hole_name not in holes:
        return None
    goal_ty, hole_ctx = holes[hole_name]
    for x, xty in hole_ctx.concrete_vars():
        if x.name in SYNTHESIS_EXCLUDED_NAMES:
            continue
        if fits(hole_ctx, xty, goal_ty):
            return TacticState(state.ctx, replace_hole(state.term, hole_name, Var(x, _loc)), state.goal)
    return None


def tactic_constructor(state: TacticState, hole_name: Name) -> TacticState | None:
    """``constructor``: intro for arrows, else first ``f : … -> goal`` spine with fresh argument holes."""
    holes = collect_hole_judgments(state.ctx, state.term, state.goal, refined_types=True)
    if hole_name not in holes:
        return None
    goal_ty, hole_ctx = holes[hole_name]

    match goal_ty:
        case AbstractionType(var_name, _, ret_type):
            vn = Name(var_name.name + "_i", fresh_counter.fresh())
            body_ty = substitution_in_type(ret_type, Var(vn), var_name)
            hn = Name("_h", fresh_counter.fresh())
            body = Annotation(Hole(hn), body_ty, loc=_loc)
            lam = Abstraction(vn, body, loc=_loc)
            return TacticState(state.ctx, replace_hole(state.term, hole_name, lam), state.goal)

    for f, fty in hole_ctx.concrete_vars():
        if f.name in SYNTHESIS_EXCLUDED_NAMES:
            continue
        params, ret = _split_arrow_spine(fty)
        if not params:
            continue
        if not fits(hole_ctx, ret, goal_ty):
            continue
        app: Term = Var(f, _loc)
        for pt in params:
            hn = Name("_h", fresh_counter.fresh())
            app = Application(app, Annotation(Hole(hn), pt, loc=_loc), loc=_loc)
        return TacticState(state.ctx, replace_hole(state.term, hole_name, app), state.goal)

    return None
