"""Existential feasibility of unfinished terms; final validation remains universal."""

from __future__ import annotations

from contextvars import ContextVar
from time import monotonic

import z3

from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidTerm, LiquidVar
from aeon.core.substitutions import liquefy, substitution_in_liquid
from aeon.core.terms import Term, Var
from aeon.core.types import RefinedType, RefinementPolymorphism, Type, TypePolymorphism, t_unit
from aeon.synthesis.grammar.nonterminals import ExpressionDomain
from aeon.synthesis.grammar.constant_constraints import conflicting_integer_equalities
from aeon.synthesis.modules.tdsyn.worklist import TypedHole, scoped_children, substitute_holes_map
from aeon.typechecking.context import TypingContext, VariableBinder
from aeon.typechecking.entailment import entailment_context
from aeon.utils.name import Name, fresh_counter
from aeon.verification.smt import flatten, translate
from aeon.verification.sub import implication_constraint
from aeon.verification.vcs import Constraint, Implication, LiquidConstraint

# Shared by candidate pruning and literal completion. A query cannot outlive
# the synthesis budget; callers outside full synthesis retain a short query cap.
deadline: ContextVar[float] = ContextVar("tdsyn_deadline", default=float("inf"))
# Stochastic walks validate only selected terms. Eager SMT pruning of every
# unchosen production can spend their entire budget before the first sample.
eager_pruning: ContextVar[bool] = ContextVar("tdsyn_eager_pruning", default=True)


def configure_solver(solver: z3.Solver) -> bool:
    remaining = deadline.get() - monotonic()
    if remaining <= 0:
        return False
    solver.set(timeout=max(1, min(500, int(remaining * 1000))) if remaining != float("inf") else 500)
    return True


def has_refinement(ty: Type) -> bool:
    return isinstance(ty, RefinedType) and ty.refinement != LiquidLiteralBool(True)


def predicate_at(ty: Type, value: LiquidTerm) -> LiquidTerm:
    if isinstance(ty, RefinedType):
        return substitution_in_liquid(ty.refinement, value, ty.name)
    return LiquidLiteralBool(True)


def symbolic_term(term: Term, holes: list[TypedHole]) -> LiquidTerm | None:
    """Value holes are existential constants, not liquid predicate unknowns."""
    return liquefy(substitute_holes_map(term, {h.name: Var(h.name) for h in holes}))


def guarded_predicate(hole: TypedHole, predicate: LiquidTerm) -> LiquidTerm:
    for guard in reversed(hole.guards):
        predicate = LiquidApp(Name("-->", 0), [guard, predicate])
    return predicate


def add_hole_binding(hole: TypedHole, bindings: dict[Name, Type], predicates: list[LiquidTerm]) -> None:
    """Declare the witness globally, but require its contract only on its path."""
    ty = hole.expected_type
    if hole.guards and isinstance(ty, RefinedType):
        bindings[hole.name] = ty.type
        predicates.append(guarded_predicate(hole, predicate_at(ty, LiquidVar(hole.name))))
    else:
        bindings[hole.name] = ty


def obligations(
    hole: TypedHole, replacement: Term, children: list[TypedHole], actual_type: Type | None = None
) -> tuple[dict[Name, Type], list[LiquidTerm]]:
    if hole.domain is ExpressionDomain.REFINEMENT:
        # Logical grammar holes describe expressions, not existential runtime
        # values. Their applications are checked at the predicate boundary.
        return {}, []
    bindings = dict(hole.bindings)
    predicates = list(hole.constraints)
    add_hole_binding(hole, bindings, predicates)
    for child in scoped_children(hole, replacement, children):
        bindings.update(child.bindings)
        predicates.extend(child.constraints)
        add_hole_binding(child, bindings, predicates)
    # Unrefined generation needs no result relation. Keep the witness types
    # for dependent siblings, but avoid turning ordinary PBT sampling into an
    # SMT query for every constructor and every unconstrained scalar.
    if not predicates and not any(has_refinement(ty) for ty in bindings.values()):
        return bindings, []
    # Closing a value hole must also constrain its pending siblings. In
    # particular, a nullary constructor's count/weight equations cannot be
    # used only for pruning and then lost before scalar model extraction.
    if actual_type is None and not children:
        from aeon.typechecking.typeinfer import synth

        _, actual_type = synth(hole.context, replacement)
    value = LiquidVar(hole.name)
    if actual_type is not None:
        predicates.append(guarded_predicate(hole, predicate_at(actual_type, value)))
    expression = symbolic_term(replacement, children)
    # Polymorphic runtime-only functions are not declared by entailment_context.
    # Their instantiated return contract above is the sound abstraction for
    # generation; inventing a logical application blocks scalar completion
    # (e.g. Array.mk_repeat's length argument). Final type checking still checks
    # the actual application, including all argument and result refinements.
    runtime_polymorphic = isinstance(expression, LiquidApp) and any(
        isinstance(entry, VariableBinder)
        and entry.name == expression.fun
        and isinstance(entry.type, (TypePolymorphism, RefinementPolymorphism))
        for entry in hole.context.entries
    )
    if expression is not None and not runtime_polymorphic:
        predicates.append(guarded_predicate(hole, LiquidApp(Name("==", 0), [value, expression])))
    return bindings, list(dict.fromkeys(p for p in predicates if p != LiquidLiteralBool(True)))


def existential_formula(ctx: TypingContext, bindings: dict[Name, Type], predicates: list[LiquidTerm]):
    """Encode Γ ∧ ∃ witnesses. contracts ∧ predicates using verification's SMT translation.

    ``translate`` produces a counterexample formula (premise ∧ ¬conclusion).
    Use each predicate as a premise and false as the conclusion to ask for a
    witness. Keeping predicates separate also lets reflection unfold each
    array read without hitting its size guard on one giant conjunction.
    """
    constraint: Constraint = LiquidConstraint(LiquidLiteralBool(False))
    for part in reversed(predicates):
        constraint = Implication(Name("_tdsyn_constraint", fresh_counter.fresh()), t_unit, part, constraint)
    for name, ty in reversed(list(bindings.items())):
        constraint = implication_constraint(name, ty, constraint)
    constraint = entailment_context(ctx, constraint)
    clauses = [translate(clause) for clause in flatten(constraint)]
    # The conclusion is false, so a vacuously valid VC means its assumptions
    # are impossible. Flattening drops that VC; it is not a feasible witness.
    return z3.And(*clauses) if clauses else z3.BoolVal(False)


def feasible(ctx: TypingContext, bindings: dict[Name, Type], predicates: list[LiquidTerm]) -> bool:
    """Prune only UNSAT. Unsupported theories and UNKNOWN retain the candidate."""
    if not predicates and not any(has_refinement(ty) for ty in bindings.values()):
        return True
    from aeon.synthesis.modules.tdsyn.incremental import solver_query

    if deadline.get() <= monotonic():
        return True
    try:
        with solver_query(ctx, bindings, predicates) as (solver, assumptions):
            if not configure_solver(solver):
                return True
            return solver.check(*assumptions) != z3.unsat
    except (AssertionError, KeyError, TypeError, ValueError, NotImplementedError, z3.Z3Exception):
        return True


def candidate_feasible(
    hole: TypedHole, replacement: Term, children: list[TypedHole], actual_type: Type | None = None
) -> bool:
    if hole.domain is ExpressionDomain.REFINEMENT:
        return True
    bindings, predicates = obligations(hole, replacement, children, actual_type)
    # Random search and GP disable expensive eager SMT queries, not the
    # elementary consistency checks that keep wrong-sized arrays out of walks.
    facts = [predicate_at(ty, LiquidVar(name)) for name, ty in bindings.items()]
    if conflicting_integer_equalities([*facts, *predicates]):
        return False
    return not eager_pruning.get() or feasible(hole.context, bindings, predicates)
