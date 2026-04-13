from __future__ import annotations


from z3 import Or, Solver, sat
from z3.z3 import ModelRef

from aeon.core.liquid import LiquidLiteralBool, LiquidVar
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.terms import Literal, Term
from aeon.core.types import (
    RefinedType,
    TypeConstructor,
    t_bool,
    t_float,
    t_int,
)
from aeon.synthesis.modules.tdsyn.helpers import base_type_of
from aeon.synthesis.modules.tdsyn.worklist import TypedHole
from aeon.typechecking.context import TypingContext, VariableBinder
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name
from aeon.verification.smt import base_functions, make_variable, translate_liq

_loc = SynthesizedLocation("tdsyn")


def _is_leaf_hole(hole: TypedHole) -> bool:
    """Check if a hole expects a base type (Int, Bool, Float) — i.e., can be filled with a literal."""
    base = base_type_of(hole.expected_type)
    if base is None:
        return False
    return base.name.name in ("Int", "Bool", "Float")


def all_leaf_holes(holes: list[TypedHole]) -> bool:
    """Check if all holes are leaf-solvable by SMT."""
    return all(_is_leaf_hole(h) for h in holes)


def _collect_context_constraints(
    ctx: TypingContext,
    z3_vars: dict[str, object],
) -> list:
    """Collect Z3 constraints from typing context variable refinements."""
    z3_constraints = []
    for entry in ctx.entries:
        match entry:
            case VariableBinder(name, RefinedType(binder, base, refinement)):
                if isinstance(base, TypeConstructor) and base.name.name in ("Int", "Bool", "Float"):
                    if refinement != LiquidLiteralBool(True):
                        # Substitute binder with variable name
                        ref = substitution_in_liquid(refinement, LiquidVar(name), binder)
                        # Make sure the context variable has a Z3 var
                        sname = str(name)
                        if sname not in z3_vars:
                            z3_vars[sname] = make_variable(sname, base)
                        try:
                            z3_c = translate_liq(ref, z3_vars | base_functions)
                            if z3_c is not None and z3_c is not True:
                                z3_constraints.append(z3_c)
                        except Exception:
                            pass
            case _:
                pass
    return z3_constraints


def solve_literals(
    holes: list[TypedHole],
    max_models: int = 5,
) -> list[dict[Name, Term]]:
    """Use Z3 to find concrete literal values for all leaf-level holes simultaneously.

    Collects constraints from:
    1. Each hole's refined expected type
    2. Each hole's propagated constraints (from parent expansions)
    3. Typing context variable refinements

    Returns a list of solutions, each mapping hole names to Literal terms.
    """
    if not holes:
        return []

    # Use the first hole's context for context constraints (they share the same scope)
    ctx = holes[0].context

    # Create Z3 variables for each hole
    z3_vars: dict[str, object] = {}
    for hole in holes:
        base = base_type_of(hole.expected_type)
        assert base is not None
        z3_vars[str(hole.name)] = make_variable(str(hole.name), base)

    # Collect constraints from context
    z3_constraints = _collect_context_constraints(ctx, z3_vars)

    # Collect constraints from each hole's expected type refinement
    for hole in holes:
        match hole.expected_type:
            case RefinedType(binder, base, refinement):
                if refinement != LiquidLiteralBool(True):
                    ref = substitution_in_liquid(refinement, LiquidVar(hole.name), binder)
                    try:
                        z3_c = translate_liq(ref, z3_vars | base_functions)
                        if z3_c is not None and z3_c is not True:
                            z3_constraints.append(z3_c)
                    except Exception:
                        pass
            case _:
                pass

        # Collect propagated constraints from parent expansions
        for constraint in hole.constraints:
            try:
                z3_c = translate_liq(constraint, z3_vars | base_functions)
                if z3_c is not None and z3_c is not True:
                    z3_constraints.append(z3_c)
            except Exception:
                pass

    if not z3_constraints:
        return []

    # Solve
    solver = Solver()
    solver.set(timeout=500)
    for c in z3_constraints:
        solver.add(c)

    solutions: list[dict[Name, Term]] = []

    for _ in range(max_models):
        result = solver.check()
        if result != sat:
            break

        model = solver.model()
        solution = _extract_solution(model, holes, z3_vars)
        if solution is not None:
            solutions.append(solution)

            # Add blocking clause to get a different solution
            blocking = []
            for hole in holes:
                z3_var = z3_vars[str(hole.name)]
                val = model[z3_var]
                if val is not None:
                    blocking.append(z3_var != val)
            if blocking:
                solver.add(Or(*blocking))
            else:
                break

    return solutions


def _extract_solution(
    model: ModelRef,
    holes: list[TypedHole],
    z3_vars: dict[str, object],
) -> dict[Name, Term] | None:
    """Extract concrete Literal terms from a Z3 model."""
    solution: dict[Name, Term] = {}

    for hole in holes:
        z3_var = z3_vars[str(hole.name)]
        val = model[z3_var]
        base = base_type_of(hole.expected_type)
        assert base is not None

        if val is None:
            # Z3 didn't constrain this variable; pick a default
            match base.name.name:
                case "Int":
                    solution[hole.name] = Literal(0, t_int, _loc)
                case "Bool":
                    solution[hole.name] = Literal(True, t_bool, _loc)
                case "Float":
                    solution[hole.name] = Literal(0.0, t_float, _loc)
                case _:
                    return None
        else:
            try:
                match base.name.name:
                    case "Int":
                        int_val = val.as_long()
                        solution[hole.name] = Literal(int_val, t_int, _loc)
                    case "Bool":
                        from z3 import is_true

                        bool_val = is_true(val)
                        solution[hole.name] = Literal(bool_val, t_bool, _loc)
                    case "Float":
                        float_val = float(val.as_decimal(10).rstrip("?"))
                        solution[hole.name] = Literal(float_val, t_float, _loc)
                    case _:
                        return None
            except Exception:
                return None

    return solution
