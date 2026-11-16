from __future__ import annotations

from aeon.core.substitutions import substitution_in_type
from aeon.core.terms import Abstraction, Annotation, Application, Hole, Rec, Term, Var
from aeon.core.types import AbstractionType, Type, type_free_term_vars
from aeon.synthesis.grammar.utils import TACTIC_CONTEXT_EXCLUDED_NAMES
from aeon.synthesis.modules.tdsyn.helpers import get_return_type, shapes_match
from aeon.synthesis.modules.tdsyn.library import get_component_library
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
        if x.name in TACTIC_CONTEXT_EXCLUDED_NAMES:
            continue
        if fits(hole_ctx, xty, goal_ty):
            nxt = state.transition(replace_hole(state.term, hole_name, Var(x, _loc)))
            if nxt is not None:
                return nxt
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
            return state.transition(replace_hole(state.term, hole_name, lam))

    library = get_component_library(hole_ctx, lambda n: n.name in TACTIC_CONTEXT_EXCLUDED_NAMES, goal_ty)
    for f, fty in library.functions_returning(goal_ty):
        # A dependent return is open until arguments are supplied. Its shape
        # selects a production; complete validation proves its refinements.
        if not shapes_match(get_return_type(fty), goal_ty):
            continue
        app: Term = f
        remaining: Type = fty
        bindings = []
        while isinstance(remaining, AbstractionType):
            pt = remaining.var_type
            hn = Name("_h", fresh_counter.fresh())
            argument: Term = Annotation(Hole(hn), pt, loc=_loc)
            later_params, _ = _split_arrow_spine(remaining.type)
            if any(remaining.var_name in type_free_term_vars(ty) for ty in later_params):
                # Give dependent siblings a real lexical binder, not a free
                # formal from the component signature.
                name = Name("_arg", fresh_counter.fresh())
                bindings.append((name, pt, argument, remaining.multiplicity))
                argument = Var(name, _loc)
                rest = substitution_in_type(remaining.type, argument, remaining.var_name)
            else:
                rest = remaining.type
            app = Application(app, argument, loc=_loc)
            remaining = rest
        for name, ty, value, multiplicity in reversed(bindings):
            app = Rec(name, ty, value, app, loc=_loc, multiplicity=multiplicity)
        nxt = state.transition(replace_hole(state.term, hole_name, app))
        if nxt is not None:
            return nxt

    return None
