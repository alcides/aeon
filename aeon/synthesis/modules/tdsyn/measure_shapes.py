"""Propose finite structures from constructor contracts and integer measures.

This is an additional search production, not a datatype specializer. A unique
measure value need not determine a unique shape: ordinary search retains all
other shapes, functions and measures that the bounded planner cannot handle.
"""

from collections.abc import Callable, Iterator
from dataclasses import dataclass, replace
from time import monotonic

import z3

from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidTerm, LiquidVar
from aeon.core.terms import Hole, Literal, RefinementApplication, Term, TypeApplication, Var
from aeon.core.types import AbstractionType, RefinedType, RefinementPolymorphism, Type, TypePolymorphism, t_int, t_unit
from aeon.synthesis.grammar.nonterminals import ExpressionDomain
from aeon.synthesis.modules.tdsyn.actions import _build_application
from aeon.synthesis.modules.tdsyn.constraints import add_hole_binding, candidate_feasible, configure_solver, deadline
from aeon.synthesis.modules.tdsyn.helpers import base_type_of, get_param_types, get_return_type, shapes_match
from aeon.synthesis.modules.tdsyn.incremental import solver_query
from aeon.synthesis.modules.tdsyn.library import get_component_library
from aeon.synthesis.modules.tdsyn.worklist import PartialAST, TypedHole, expand_at_hole
from aeon.utils.name import Name, fresh_counter
from aeon.verification.smt import make_variable

# Bound only the extra proposal's allocation/work, never ordinary search.
MAX_MEASURE = 256
MAX_PLAN_NODES = 512


def goal_measures(hole: TypedHole) -> Iterator[Name]:
    """Find unary integer measures applied to the goal's refinement binder."""
    goal = hole.expected_type
    base = base_type_of(goal)
    if hole.domain is not ExpressionDomain.TERM or base is None or not isinstance(goal, RefinedType):
        return
    pending = [goal.refinement]
    seen = set()
    while pending:
        expression = pending.pop()
        if not isinstance(expression, LiquidApp):
            continue
        pending.extend(reversed(expression.args))
        if expression.args != [LiquidVar(goal.name)] or expression.fun in seen:
            continue
        seen.add(expression.fun)
        signature = hole.context.type_of(expression.fun)
        while isinstance(signature, (TypePolymorphism, RefinementPolymorphism)):
            signature = signature.body
        if isinstance(signature, AbstractionType) and signature.type == t_int:
            argument = base_type_of(signature.var_type)
            if argument is not None and argument.name == base.name:
                yield expression.fun


def fixed_measure(hole: TypedHole, measure: Name) -> int | None:
    """Prove a bounded unique measure value, rather than trust one SMT model."""
    if monotonic() >= deadline.get():
        return None
    bindings, predicates = dict(hole.bindings), list(hole.constraints)
    add_hole_binding(hole, bindings, predicates)
    probe = Name("tdsyn_measure", fresh_counter.fresh())
    bindings[probe] = t_int
    predicates.append(LiquidApp(Name("==", 0), [LiquidVar(probe), LiquidApp(measure, [LiquidVar(hole.name)])]))
    try:
        with solver_query(hole.context, bindings, predicates) as (solver, assumptions):
            if not configure_solver(solver) or solver.check(*assumptions) != z3.sat:
                return None
            variable = make_variable(str(probe), t_int)
            value = solver.model().eval(variable, model_completion=True)
            if not z3.is_int_value(value) or not 0 <= value.as_long() <= MAX_MEASURE:
                return None
            rank = value.as_long()
            solver.add(variable != rank)
            if configure_solver(solver) and solver.check(*assumptions) == z3.unsat:
                return rank
    except (AssertionError, KeyError, TypeError, ValueError, NotImplementedError, z3.Z3Exception):
        pass
    return None


def _conjuncts(expression: LiquidTerm) -> Iterator[LiquidTerm]:
    if isinstance(expression, LiquidApp) and expression.fun == Name("&&", 0):
        for argument in expression.args:
            yield from _conjuncts(argument)
    else:
        yield expression


def _affine(expression: LiquidTerm, measure: Name, parameters: list[Name]) -> tuple[int, tuple[int, ...]] | None:
    """Read constants and affine combinations of the same measure on children.

    Scalar payloads and unrelated/nonlinear measures deliberately stay in the
    ordinary search. Payload values must not be mistaken for structural sizes.
    """
    if isinstance(expression, LiquidLiteralInt):
        return expression.value, (0,) * len(parameters)
    if not isinstance(expression, LiquidApp):
        return None
    if expression.fun == measure and len(expression.args) == 1:
        argument = expression.args[0]
        if isinstance(argument, LiquidVar) and argument.name in parameters:
            return 0, tuple(int(name == argument.name) for name in parameters)
    if len(expression.args) != 2:
        return None
    left = _affine(expression.args[0], measure, parameters)
    right = _affine(expression.args[1], measure, parameters)
    if left is None or right is None:
        return None
    if expression.fun in (Name("+", 0), Name("-", 0)):
        sign = 1 if expression.fun == Name("+", 0) else -1
        return left[0] + sign * right[0], tuple(a + sign * b for a, b in zip(left[1], right[1]))
    if expression.fun == Name("*", 0):
        if not any(left[1]):
            return left[0] * right[0], tuple(left[0] * c for c in right[1])
        if not any(right[1]):
            return right[0] * left[0], tuple(right[0] * c for c in left[1])
    return None


@dataclass(frozen=True)
class Production:
    name: Name
    term: Term
    signature: Type
    offset: int
    # (parameter index, positive coefficient) for every recursive field.
    children: tuple[tuple[int, int], ...]


def _productions(hole: TypedHole, skip: Callable[[Name], bool], measure: Name) -> Iterator[Production]:
    library = get_component_library(hole.context, skip, hole.nonterminal)
    for term, signature in (
        *library.values_matching(hole.expected_type),
        *library.functions_returning(hole.expected_type),
    ):
        result = get_return_type(signature)
        if not isinstance(result, RefinedType) or not shapes_match(result, hole.expected_type):
            continue
        head = term
        while isinstance(head, (TypeApplication, RefinementApplication)):
            head = head.body
        if not isinstance(head, Var):
            continue
        parameters = get_param_types(signature)
        recursive = [(i, name) for i, (name, ty) in enumerate(parameters) if shapes_match(ty, result)]
        measured_result = LiquidApp(measure, [LiquidVar(result.name)])
        for predicate in _conjuncts(result.refinement):
            if not isinstance(predicate, LiquidApp) or predicate.fun != Name("==", 0) or len(predicate.args) != 2:
                continue
            left, right = predicate.args
            expression = right if left == measured_result else left if right == measured_result else None
            affine = _affine(expression, measure, [name for _, name in recursive]) if expression is not None else None
            if affine is None:
                continue
            offset, coefficients = affine
            if offset < 0 or any(c <= 0 for c in coefficients):
                continue
            children = tuple((index, c) for (index, _), c in zip(recursive, coefficients))
            yield Production(head.name, term, signature, offset, children)
            break


@dataclass(frozen=True)
class Plan:
    production: Production
    children: tuple["Plan", ...]
    cost: int


def _plan(productions: list[Production], target: int) -> Plan | None:
    """Dynamic programming over strictly smaller, nonnegative child measures.

    Minimize structural applications. For ambiguous branching this offers one
    cheap representative; it does not claim that the shape is unique.
    """
    plans: dict[int, Plan] = {}
    for rank in range(target + 1):
        for production in productions:
            if monotonic() >= deadline.get():
                return None
            remaining = rank - production.offset
            if remaining < 0:
                continue
            # Bounded convolution avoids enumerating a Cartesian product of
            # all child ranks for constructors with many recursive fields.
            combinations: dict[int, tuple[int, tuple[Plan, ...]]] = {0: (1, ())}
            for _, coefficient in production.children:
                following: dict[int, tuple[int, tuple[Plan, ...]]] = {}
                for subtotal, (cost, children) in combinations.items():
                    for child_rank in reversed(range(min(rank, (remaining - subtotal) // coefficient + 1))):
                        child = plans.get(child_rank)
                        if child is None:
                            continue
                        total, new_cost = subtotal + coefficient * child_rank, cost + child.cost
                        if new_cost <= MAX_PLAN_NODES and (total not in following or new_cost < following[total][0]):
                            following[total] = (new_cost, (*children, child))
                combinations = following
            combination = combinations.get(remaining)
            if combination is not None and (rank not in plans or combination[0] < plans[rank].cost):
                plans[rank] = Plan(production, combination[1], combination[0])
    return plans.get(target)


def _materialize(
    hole: TypedHole, skip: Callable[[Name], bool], measure: Name, plan: Plan
) -> tuple[Term, list[TypedHole]] | None:
    root = replace(hole, path=())
    partial = PartialAST(Hole(root.name), [root], 0)
    pending = [(root.name, plan)]
    while pending:
        if monotonic() >= deadline.get():
            return None
        name, current_plan = pending.pop()
        current = next(h for h in partial.holes if h.name == name)
        # Reinstantiate at the actual child type: relations can depend on an
        # earlier payload. Reusing the root signature would lose that contract.
        original = current_plan.production
        production = next(
            (
                p
                for p in _productions(current, skip, measure)
                if p.name == original.name and p.offset == original.offset and p.children == original.children
            ),
            None,
        )
        if production is None:
            return None
        if isinstance(production.signature, AbstractionType):
            term, children = _build_application(production.term, production.signature, current)
        else:
            term, children = production.term, []
        partial = expand_at_hole(partial, current, term, children, partial.depth + 1)
        pending.extend(
            reversed(
                [
                    (children[index].name, child_plan)
                    for (index, _), child_plan in zip(production.children, current_plan.children)
                ]
            )
        )
        if len(partial.holes) > MAX_PLAN_NODES:
            return None
    # Unit has only one inhabitant and is not a structural choice.
    for child in list(partial.holes):
        if base_type_of(child.expected_type) == t_unit:
            partial = expand_at_hole(partial, child, Literal(None, t_unit), [], partial.depth)
    if candidate_feasible(hole, partial.term, partial.holes):
        return partial.term, partial.holes
    return None


def measure_shape_candidates(hole: TypedHole, skip: Callable[[Name], bool]) -> list[tuple[Term, list[TypedHole]]]:
    for measure in goal_measures(hole):
        rank = fixed_measure(hole, measure)
        if rank is None:
            continue
        plan = _plan(list(_productions(hole, skip, measure)), rank)
        if plan is not None:
            candidate = _materialize(hole, skip, measure, plan)
            if candidate is not None:
                return [candidate]
    return []


def iter_measure_shape_candidates(
    hole: TypedHole, skip: Callable[[Name], bool]
) -> Iterator[tuple[Term, list[TypedHole]]]:
    # Keep proof and planning inside the lazy scheduler's budget/error handling.
    yield from measure_shape_candidates(hole, skip)
