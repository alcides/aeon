from __future__ import annotations


from z3 import BoolRef, Length, Not, Or, Solver, StrToCode, SubString, sat, unsat
from z3.z3types import Z3Exception
from z3.z3 import ModelRef

from aeon.core.liquid import LiquidTerm
from aeon.core.substitutions import liquefy, substitution_in_liquid
from aeon.core.terms import Literal, Term
from aeon.core.types import (
    RefinedType,
    Type,
    t_bool,
    t_float,
    t_int,
    t_string,
)
from aeon.synthesis.modules.tdsyn.helpers import base_type_of
from aeon.synthesis.grammar.nonterminals import ExpressionDomain
from aeon.synthesis.modules.tdsyn.constraints import configure_solver, has_refinement
from aeon.synthesis.modules.tdsyn.incremental import solver_query
from aeon.synthesis.modules.tdsyn.worklist import TypedHole
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name
from aeon.verification.smt import base_functions, make_variable, translate_liq

_loc = SynthesizedLocation("tdsyn")


def literal_satisfies(term: Term, ty: RefinedType) -> bool:
    """Validate a generated literal with the same SMT translation as completion.

    Minimal generation contexts have no executable operators or helpers. Check
    the closed, substituted predicate instead of assuming a grammar terminal is
    a proof. Unknown/unsupported refinements fail closed.
    """
    if not isinstance(term, Literal) or term.type != ty.type:
        return False
    value = liquefy(term)
    if value is None:
        return False
    predicate = substitution_in_liquid(ty.refinement, value, ty.name)
    try:
        solver = Solver()
        solver.set(timeout=500)
        solver.add(Not(translate_liq(predicate, base_functions)))
        return solver.check() == unsat
    except (AssertionError, KeyError, TypeError, ValueError, Z3Exception):
        return False


def _is_leaf_hole(hole: TypedHole) -> bool:
    """Check whether a hole can be completed by an SMT-backed base literal."""
    if hole.domain is ExpressionDomain.REFINEMENT:
        return False
    base = base_type_of(hole.expected_type)
    if base is None:
        return False
    return base.name.name in ("Int", "Bool", "Float", "String")


def all_leaf_holes(holes: list[TypedHole]) -> bool:
    """Check if all holes are leaf-solvable by SMT."""
    return all(_is_leaf_hole(h) for h in holes)


def solve_literals(
    holes: list[TypedHole],
    max_models: int = 5,
) -> list[dict[Name, Term]]:
    """Solve scalar leaves jointly, retaining dependent and datatype constraints.

    The shared existential encoding includes all previously introduced witness
    bindings. Unsupported predicates are never silently removed from a model
    query: leave the holes open for ordinary search and final validation.
    """
    if not holes or any(h.domain is ExpressionDomain.REFINEMENT for h in holes):
        return []
    bindings: dict[Name, Type] = {}
    predicates: list[LiquidTerm] = []
    for hole in holes:
        bindings.update(hole.bindings)
        bindings[hole.name] = hole.expected_type
        predicates.extend(hole.constraints)
    if not predicates and not any(has_refinement(ty) for ty in bindings.values()):
        return []
    try:
        with solver_query(holes[0].context, bindings, list(dict.fromkeys(predicates))) as (solver, assumptions):
            z3_vars = {}
            for hole in holes:
                base = base_type_of(hole.expected_type)
                assert base is not None
                z3_vars[str(hole.name)] = make_variable(str(hole.name), base)
            return _literal_models(solver, assumptions, holes, z3_vars, max_models)
    except (AssertionError, KeyError, TypeError, ValueError, NotImplementedError, Z3Exception):
        return []


def _literal_models(
    solver: Solver,
    assumptions: list[BoolRef],
    holes: list[TypedHole],
    z3_vars: dict[str, object],
    max_models: int,
) -> list[dict[Name, Term]]:
    solutions: list[dict[Name, Term]] = []
    for _ in range(max_models):
        if not configure_solver(solver) or solver.check(*assumptions) != sat:
            break
        model = solver.model()
        solution = _extract_solution(model, holes, z3_vars)
        if solution is None:
            break
        solutions.append(solution)
        blocking = []
        for hole in holes:
            var = z3_vars[str(hole.name)]
            val = model[var]
            if val is not None:
                blocking.append(var != val)
        if not blocking:
            break
        solver.add(Or(*blocking))
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
                case "String":
                    solution[hole.name] = Literal("", t_string, _loc)
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
                    case "String":
                        # as_string() renders non-ASCII codepoints as textual
                        # \\u{...} escapes, changing their Python length. Decode
                        # model characters, not Z3's display representation.
                        length = model.eval(Length(val)).as_long()
                        value = "".join(
                            chr(model.eval(StrToCode(SubString(val, i, 1))).as_long()) for i in range(length)
                        )
                        solution[hole.name] = Literal(value, t_string, _loc)
                    case _:
                        return None
            except Exception:
                return None

    return solution
