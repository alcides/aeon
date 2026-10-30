"""Three-valued SMT queries and finite, weakest-valuation Horn solving.

Unlike verification/horn.py this solver starts at True and strengthens negative
predicate occurrences. MUS enumeration uses MARCO's subset/superset blocking
with deletion-based minimisation (an oracle variant of MUSFIX, PLDI'16 §3.6).
An incomplete enumeration is UNKNOWN, never evidence of incompatibility.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Callable
from time import monotonic

import z3

from aeon.core.liquid import LiquidTerm
from aeon.core.types import LiquidHornApplication, Top, builtin_core_types, t_bool
from aeon.core.liquid_ops import liquid_prelude
from aeon.typechecking.liquid import (
    LiquidTypeCheckingContext,
    LiquidTypeCheckException,
    check_liquid,
    lower_abstraction_type,
)
from aeon.utils.name import Name
from aeon.verification.horn import (
    Assignment,
    apply_constraint,
    apply_liquid,
    obtain_holes,
    split,
)
from aeon.verification.smt import flatten, translate
from aeon.verification.vcs import (
    Constraint,
    Conjunction,
    Implication,
    LiquidConstraint,
    ReflectedFunctionDeclaration,
    UninterpretedFunctionDeclaration,
)


class Status(Enum):
    VALID = "valid"
    INVALID = "invalid"
    UNKNOWN = "unknown"
    UNSUPPORTED = "unsupported"
    EXHAUSTED = "qualifiers exhausted"
    INCONSISTENT = "inconsistent context"


@dataclass
class SearchStats:
    argument_candidates: int = 0
    partial_rejections: int = 0
    complete_rejections: int = 0
    full_validations: int = 0
    abduction_branches: int = 0
    abduced_guards: int = 0
    fallback_guards: int = 0
    solver_queries: int = 0
    outcomes: dict[str, int] = field(default_factory=dict)

    def record(self, status: Status) -> Status:
        self.outcomes[status.value] = self.outcomes.get(status.value, 0) + 1
        return status


def _well_sorted(c: Constraint, ctx: LiquidTypeCheckingContext) -> bool:
    if isinstance(c, LiquidConstraint):
        return check_liquid(ctx, c.expr, t_bool)
    if isinstance(c, Conjunction):
        return _well_sorted(c.c1, ctx) and _well_sorted(c.c2, ctx)
    if isinstance(c, Implication):
        if isinstance(c.base, Top):
            return False
        inner = LiquidTypeCheckingContext(ctx.known_types, {**ctx.variables, c.name: c.base}, ctx.functions)
        return check_liquid(inner, c.pred, t_bool) and _well_sorted(c.seq, inner)
    if isinstance(c, (UninterpretedFunctionDeclaration, ReflectedFunctionDeclaration)):
        inner = LiquidTypeCheckingContext(
            ctx.known_types, ctx.variables, {**ctx.functions, c.name: lower_abstraction_type(c.type)}
        )
        return _well_sorted(c.seq, inner)
    return False


@dataclass
class SMTQuery:
    timeout_ms: int = 100
    stats: SearchStats = field(default_factory=SearchStats)
    deadline: float = float("inf")

    def valid(self, constraint: Constraint) -> Status:
        """Only SAT counterexamples disprove a VC. Unknown is not False."""
        if monotonic() >= self.deadline:
            return Status.UNKNOWN
        try:
            if not _well_sorted(constraint, LiquidTypeCheckingContext(builtin_core_types, {}, dict(liquid_prelude))):
                return Status.UNSUPPORTED
            solver = z3.Solver()
            solver.set(timeout=self.timeout_ms)
            for clause in flatten(constraint):
                solver.push()
                try:
                    solver.add(translate(clause))
                    self.stats.solver_queries += 1
                    answer = solver.check()
                    if answer == z3.sat:
                        return Status.INVALID
                    if answer == z3.unknown:
                        return Status.UNKNOWN
                finally:
                    solver.pop()
            return Status.VALID
        except (
            LiquidTypeCheckException,
            AssertionError,
            KeyError,
            TypeError,
            ValueError,
            NotImplementedError,
            z3.Z3Exception,
            ZeroDivisionError,
        ):
            return Status.UNSUPPORTED


@dataclass(frozen=True)
class Predicate:
    occurrence: LiquidHornApplication
    qualifiers: tuple[LiquidTerm, ...]
    # Γ => !κ: INVALID means Γ && κ has an inhabitant.
    nonempty: Constraint


@dataclass
class Solutions:
    assignments: list[Assignment]
    status: Status


def minimal_subsets(
    count: int,
    proves: Callable[[frozenset[int]], Status],
    *,
    max_checks: int = 256,
) -> tuple[list[frozenset[int]], Status]:
    """Enumerate MUSes relative to a fixed negated conclusion.

    ``proves(S)`` tests unsatisfiability of premise ∧ S ∧ ¬conclusion.
    Shrink a valid seed to a MUS; block its supersets. Grow an invalid seed to
    an MSS; block its subsets. No bound on conjunction width is imposed.
    """
    selector = z3.Solver()
    bits = [z3.Bool(f"select_{i}") for i in range(count)]
    cache: dict[frozenset[int], Status] = {}
    found: list[frozenset[int]] = []

    def query(indices: frozenset[int]) -> Status:
        if indices not in cache:
            if len(cache) >= max_checks:
                return Status.UNKNOWN
            cache[indices] = proves(indices)
        return cache[indices]

    while True:
        selection = selector.check()
        if selection == z3.unsat:
            return found, Status.VALID
        if selection == z3.unknown:
            return found, Status.UNKNOWN
        model = selector.model()
        seed = frozenset(i for i, bit in enumerate(bits) if z3.is_true(model.eval(bit, model_completion=True)))
        result = query(seed)
        if result == Status.VALID:
            for i in sorted(seed):
                trial = seed - {i}
                result = query(trial)
                if result == Status.VALID:
                    seed = trial
                elif result != Status.INVALID:
                    return found, result
            found.append(seed)
            selector.add(z3.Or([z3.Not(bits[i]) for i in seed]))
        elif result == Status.INVALID:
            for i in range(count):
                if i in seed:
                    continue
                trial = seed | {i}
                result = query(trial)
                if result == Status.INVALID:
                    seed = trial
                elif result != Status.VALID:
                    return found, result
            selector.add(z3.Or([bits[i] for i in range(count) if i not in seed]))
        else:
            return found, result


def _negative_holes(c: Constraint) -> list[LiquidHornApplication]:
    if isinstance(c, Implication):
        return obtain_holes(c.pred) + _negative_holes(c.seq)
    if isinstance(c, (UninterpretedFunctionDeclaration, ReflectedFunctionDeclaration)):
        return _negative_holes(c.seq)
    return []


def _freeze_head(c: Constraint, assignment: Assignment) -> Constraint:
    if isinstance(c, LiquidConstraint):
        return LiquidConstraint(apply_liquid(assignment, c.expr))
    if isinstance(c, Implication):
        return Implication(c.name, c.base, c.pred, _freeze_head(c.seq, assignment))
    if isinstance(c, UninterpretedFunctionDeclaration):
        return UninterpretedFunctionDeclaration(c.name, c.type, _freeze_head(c.seq, assignment))
    if isinstance(c, ReflectedFunctionDeclaration):
        return ReflectedFunctionDeclaration(c.name, c.type, c.params, c.body, _freeze_head(c.seq, assignment))
    raise NotImplementedError(type(c))


def weakest_assignments(
    constraints: tuple[Constraint, ...],
    predicates: dict[Name, Predicate],
    initial: list[Assignment],
    query: SMTQuery,
    *,
    max_checks: int = 256,
) -> Solutions:
    """Incremental greatest fixpoint, retaining incomparable strengthenings.

    Qualifiers use Horn's canonical argument names, so substitutions and sort
    checking are shared with verification. The verification solver is unchanged.
    """
    clauses = [clause for c in constraints for clause in split(c)]
    todo = [{**{n: [] for n in predicates}, **a} for a in initial]
    solutions: list[Assignment] = []
    visited: set[tuple] = set()
    incomplete: Status | None = None
    while todo:
        assignment = todo.pop()
        key = tuple((n, tuple(assignment[n])) for n in sorted(assignment, key=str))
        if key in visited:
            continue
        visited.add(key)
        if len(visited) > max_checks:
            incomplete = Status.UNKNOWN
            break
        for predicate in predicates.values():
            nonempty = query.valid(apply_constraint(assignment, predicate.nonempty))
            if nonempty != Status.INVALID:
                if nonempty != Status.VALID:
                    incomplete = nonempty
                break
        else:
            for clause in clauses:
                result = query.valid(apply_constraint(assignment, clause))
                if result == Status.VALID:
                    continue
                if result != Status.INVALID:
                    incomplete = result
                    break
                negative = {h.name for h in _negative_holes(clause)}
                choices = [
                    (n, q)
                    for n in sorted(negative, key=str)
                    if n in predicates
                    for q in predicates[n].qualifiers
                    if q not in assignment[n]
                ]
                frozen = _freeze_head(clause, assignment)

                def strengthen(indices: frozenset[int]) -> Assignment:
                    out = {n: list(qs) for n, qs in assignment.items()}
                    for i in sorted(indices):
                        n, q = choices[i]
                        out[n].append(q)
                    return out

                subsets, status = minimal_subsets(
                    len(choices),
                    lambda indices: query.valid(apply_constraint(strengthen(indices), frozen)),
                    max_checks=max_checks,
                )
                if status != Status.VALID:
                    incomplete = status
                todo.extend(strengthen(indices) for indices in subsets if indices)
                break
            else:
                solutions.append(assignment)
    return Solutions(solutions, incomplete or (Status.VALID if solutions else Status.EXHAUSTED))
