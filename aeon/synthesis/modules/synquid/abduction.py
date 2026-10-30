"""Branch-first IFAB: solve Γ, κ ⊢ branch : goal before constructing a guard."""

from __future__ import annotations

from dataclasses import dataclass

from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidTerm
from aeon.core.substitutions import liquefy
from aeon.core.terms import Annotation, Application, Literal, Term, Var
from aeon.core.types import Type, t_bool
from aeon.errors import CoreTypeCheckingError
from aeon.typechecking.liquid import LiquidTypeCheckException
from aeon.synthesis.modules.synquid.constraints import ConstraintState
from aeon.synthesis.modules.synquid.guards import bool_terms_from_qualifier_atoms
from aeon.synthesis.modules.synquid.solver import Status
from aeon.typechecking.qualifiers import extract_qualifier_atoms
from aeon.typechecking.typeinfer import check
from aeon.utils.name import Name
from aeon.verification.horn import apply_liquid
from aeon.verification.vcs import LiquidConstraint


@dataclass
class AbductionResult:
    guards: list[tuple[LiquidTerm, Term]]
    status: Status


def branch_environment(state: ConstraintState, goal: Type) -> ConstraintState:
    """Permit branch-local preconditions to constrain κ during construction."""
    child = state.fork()
    atoms = extract_qualifier_atoms(child.context, goal_type=goal)
    terms = bool_terms_from_qualifier_atoms(child.context, atoms)
    qualifiers = frozenset(liquid for term in terms if (liquid := liquefy(term)) is not None)
    predicate = child.fresh_predicate(child.context, qualifiers)
    return child.assume(predicate)


def abduce(
    state: ConstraintState,
    branch: Term,
    goal: Type,
    *,
    qualifiers: frozenset[LiquidTerm] | None = None,
) -> AbductionResult:
    state.stats.abduction_branches += 1
    ctx = state.context
    if state.inhabited() == Status.VALID:
        return AbductionResult([], Status.INCONSISTENT)
    atoms = extract_qualifier_atoms(ctx, goal_type=goal)
    terms = bool_terms_from_qualifier_atoms(ctx, atoms | (qualifiers or frozenset()))
    realizations = {liquid: term for term in terms if (liquid := liquefy(term)) is not None}
    if qualifiers is None:
        qualifiers = frozenset(realizations)
    branch_state = state.fork()
    try:
        predicate = branch_state.fresh_predicate(ctx, qualifiers)
        branch_state = branch_state.assume(predicate)
        branch_state.add(check(branch_state.context, branch, goal))
        status = branch_state.solve()
    except (
        AssertionError,
        KeyError,
        TypeError,
        ValueError,
        NotImplementedError,
        CoreTypeCheckingError,
        LiquidTypeCheckException,
    ):
        return AbductionResult([], Status.UNSUPPORTED)
    if status != Status.VALID:
        return AbductionResult([], status)
    guards: list[LiquidTerm] = []
    for assignment in branch_state.assignments:
        guard = apply_liquid(assignment, predicate)
        # Semantic minimisation: discard stronger guards and collapse equivalent
        # ones deterministically; retain incomparable weakest alternatives.
        if any(
            state.assume(guard).query.valid(state.assume(guard).lift(LiquidConstraint(g))) == Status.VALID
            for g in guards
        ):
            continue
        guards = [
            g
            for g in guards
            if state.assume(g).query.valid(state.assume(g).lift(LiquidConstraint(guard))) != Status.VALID
        ]
        guards.append(guard)

    def realize(guard: LiquidTerm) -> Term | None:
        if isinstance(guard, LiquidLiteralBool):
            return Literal(guard.value, t_bool)
        if guard in realizations:
            term = realizations[guard]
            return term.expr if isinstance(term, Annotation) else term
        if isinstance(guard, LiquidApp) and guard.fun == Name("&&", 0):
            left, right = (realize(g) for g in guard.args)
            if left is not None and right is not None:
                return Application(Application(Var(guard.fun), left), right)
        return None

    realized = [(g, t) for g in guards if (t := realize(g)) is not None]
    if len(realized) != len(guards):
        # A logical solution without a Boolean program is not a completed
        # abduction. Keep successful realizations and enable the fallback.
        status = Status.UNSUPPORTED
    return AbductionResult(realized, status)
