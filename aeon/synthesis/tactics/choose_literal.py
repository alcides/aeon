from __future__ import annotations

from aeon.core.liquid import LiquidLiteralBool
from aeon.core.terms import Literal, Term
from aeon.core.types import RefinedType, Type, TypeConstructor, t_bool, t_float, t_int
from aeon.synthesis.modules.tdsyn.helpers import base_type_of
from aeon.synthesis.modules.tdsyn.smt_solve import solve_literals
from aeon.synthesis.modules.tdsyn.worklist import TypedHole
from aeon.synthesis.tactics.holes import collect_hole_judgments, replace_hole
from aeon.synthesis.tactics.state import TacticState
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name

_loc = SynthesizedLocation("tactics")

_LEAF_BASE_NAMES = frozenset({"Int", "Bool", "Float"})


def _refinement_is_non_trivial(ty: Type) -> bool:
    match ty:
        case RefinedType(_, _, ref):
            return ref != LiquidLiteralBool(True)
        case _:
            return False


def _default_literal(base: TypeConstructor) -> Term | None:
    match base.name.name:
        case "Int":
            return Literal(0, t_int, _loc)
        case "Bool":
            return Literal(True, t_bool, _loc)
        case "Float":
            return Literal(0.0, t_float, _loc)
        case _:
            return None


def tactic_choose_literal(state: TacticState, hole_name: Name) -> TacticState | None:
    """Fill a leaf hole with a Z3 model of its (refined) type, if possible.

    Uses the same encoding as TDSyn's ``solve_literals`` (context refinements +
    hole refinement). If Z3 finds no model and the goal carries a non-trivial
    refinement, the tactic fails. If there is no non-trivial refinement and Z3
    yields no constraints, falls back to a simple default (0 / true / 0.0).
    """
    holes = collect_hole_judgments(state.ctx, state.term, state.goal, refined_types=True)
    if hole_name not in holes:
        return None
    goal_ty, hole_ctx = holes[hole_name]

    base = base_type_of(goal_ty)
    if base is None or base.name.name not in _LEAF_BASE_NAMES:
        return None

    th = TypedHole(hole_name, goal_ty, hole_ctx, [])
    solutions = solve_literals([th], max_models=1)
    lit: Term | None = None
    if solutions and hole_name in solutions[0]:
        lit = solutions[0][hole_name]

    if lit is None:
        if _refinement_is_non_trivial(goal_ty):
            return None
        lit = _default_literal(base)
        if lit is None:
            return None

    return TacticState(state.ctx, replace_hole(state.term, hole_name, lit), state.goal)
