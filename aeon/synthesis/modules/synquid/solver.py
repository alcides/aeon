"""Three-valued SMT queries and finite, weakest-valuation Horn solving.

Unlike verification/horn.py this solver starts at True and strengthens negative
predicate occurrences. MUSFIX uses tracked SMT unsat cores, MARCO's Boolean
subset map, and semantic minimization of alternative valuations (PLDI'16 §3.6).
An incomplete enumeration is UNKNOWN, never evidence of incompatibility.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Callable
from time import monotonic

import z3

from aeon.core.liquid import LiquidTerm, LiquidApp, LiquidVar, LiquidLiteralBool
from aeon.core.types import LiquidHornApplication, Top, TypeConstructor, TypeVar, builtin_core_types, t_bool
from aeon.core.liquid_ops import liquid_prelude
from aeon.typechecking.liquid import (
    LiquidTypeCheckingContext,
    LiquidTypeCheckException,
    check_liquid,
    lower_abstraction_type,
)
from aeon.utils.name import Name, fresh_counter
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
    unsat_cores: int = 0
    matches: int = 0
    match_abductions: int = 0
    recursive_functions: int = 0
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

        def schema_sort(ty):
            # VC declarations encode quantified type variables as lowercase
            # nullary constructors (the SMT specialisation convention).
            if isinstance(ty, TypeConstructor):
                if not ty.args and ty.name.name[:1].islower():
                    return TypeVar(ty.name)
                return TypeConstructor(ty.name, [schema_sort(a) for a in ty.args])
            return ty

        inner = LiquidTypeCheckingContext(
            ctx.known_types,
            ctx.variables,
            {**ctx.functions, c.name: [schema_sort(t) for t in lower_abstraction_type(c.type)]},
        )
        return _well_sorted(c.seq, inner)
    return False


@dataclass
class SMTQuery:
    timeout_ms: int = 0
    stats: SearchStats = field(default_factory=SearchStats)
    deadline: float = float("inf")
    liquid_context: LiquidTypeCheckingContext | None = None

    def valid(self, constraint: Constraint) -> Status:
        """Only SAT counterexamples disprove a VC. Unknown is not False."""
        if monotonic() >= self.deadline:
            return Status.UNKNOWN
        try:
            if not _well_sorted(
                constraint,
                self.liquid_context or LiquidTypeCheckingContext(builtin_core_types, {}, dict(liquid_prelude)),
            ):
                return Status.UNSUPPORTED
            solver = z3.Solver()
            self.configure(solver)
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

    def configure(self, solver: z3.Solver) -> None:
        remaining = max(1, int((self.deadline - monotonic()) * 1000)) if self.deadline != float("inf") else 0
        timeout = min(self.timeout_ms, remaining) if self.timeout_ms and remaining else self.timeout_ms or remaining
        solver.set(timeout=timeout)


class StrengtheningOracle:
    """One incremental SMT query, with a tracked assumption per qualifier.

    The negated Horn head is fixed. Unselected qualifiers can be disabled;
    unsat cores therefore identify subsets sufficient to prove this head.
    Qualifiers are tagged by their predicate, preserving every partition of a
    MUS among unknowns even when two predicates have the same atom.
    """

    def __init__(self, clause, assignment, choices, query):
        self.query = query
        self.names = [Name("_sq_select", fresh_counter.fresh()) for _ in choices]
        self.bits = [z3.Bool(str(n)) for n in self.names]
        symbolic = {n: list(qs) for n, qs in assignment.items()}
        for selector, (name, qualifier) in zip(self.names, choices):
            symbolic[name].append(LiquidApp(Name("-->", 0), [LiquidVar(selector), qualifier]))
        constraint = apply_constraint(symbolic, clause)
        for name in self.names:
            constraint = Implication(name, t_bool, LiquidLiteralBool(True), constraint)
        self.solver = z3.Solver()
        self.query.configure(self.solver)
        self.solver.add(z3.Or([translate(c) for c in flatten(constraint)]))

        def erase_head(c):
            from dataclasses import replace

            if isinstance(c, LiquidConstraint):
                return LiquidConstraint(LiquidLiteralBool(False))
            if isinstance(c, Conjunction):
                return Conjunction(erase_head(c.c1), erase_head(c.c2))
            return replace(c, seq=erase_head(c.seq))

        self.premises = z3.Solver()
        self.premises.add(z3.Or([translate(c) for c in flatten(erase_head(constraint))]))
        self.last_core: frozenset[int] = frozenset()

    def __call__(self, indices):
        if monotonic() >= self.query.deadline:
            return Status.UNKNOWN
        self.query.configure(self.solver)
        self.query.stats.solver_queries += 1
        answer = self.solver.check(*[self.bits[i] for i in sorted(indices)])
        if answer == z3.unsat:
            core = {str(b) for b in self.solver.unsat_core()}
            self.last_core = frozenset(i for i in indices if str(self.bits[i]) in core)
            self.query.stats.unsat_cores += 1
            return Status.VALID
        return Status.INVALID if answer == z3.sat else Status.UNKNOWN

    def core(self, indices):
        # Cached oracle answers need not refer to the last solver query.
        status = self(indices)
        return self.last_core if status == Status.VALID else indices

    def consistent(self, indices):
        """The negated head must be essential to the MUS (paper §3.6).

        Individual predicate nonemptiness does not rule out a contradiction
        between two predicates occurring together in this Horn premise.
        """
        if monotonic() >= self.query.deadline:
            return Status.UNKNOWN
        self.query.configure(self.premises)
        self.query.stats.solver_queries += 1
        result = self.premises.check(*[self.bits[i] for i in sorted(indices)])
        return Status.VALID if result == z3.sat else Status.INCONSISTENT if result == z3.unsat else Status.UNKNOWN


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
    max_checks: int | None = None,
    implies: dict[int, frozenset[int]] | None = None,
    impossible: frozenset[int] = frozenset(),
) -> tuple[list[frozenset[int]], Status]:
    """Enumerate MUSes relative to a fixed negated conclusion.

    ``proves(S)`` tests unsatisfiability of premise ∧ S ∧ ¬conclusion.
    Shrink a valid seed to a MUS; block its supersets. Grow an invalid seed to
    an MSS; block its subsets. No bound on conjunction width is imposed.
    """
    selector = z3.Solver()
    bits = [z3.Bool(f"select_{i}") for i in range(count)]
    for i in impossible:
        selector.add(z3.Not(bits[i]))
    cache: dict[frozenset[int], Status] = {}
    found: list[frozenset[int]] = []

    def query(indices: frozenset[int]) -> Status:
        if indices not in cache:
            if max_checks is not None and len(cache) >= max_checks:
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
            if isinstance(proves, StrengtheningOracle):
                seed = proves.core(seed)
            for i in sorted(seed):
                trial = seed - {i}
                result = query(trial)
                if result == Status.VALID:
                    seed = trial
                elif result != Status.INVALID:
                    return found, result
            consistency = proves.consistent(seed) if isinstance(proves, StrengtheningOracle) else Status.VALID
            if consistency == Status.VALID:
                found.append(seed)
            elif consistency != Status.INCONSISTENT:
                return found, consistency
            # Block semantic supersets as well as syntactic ones. Each atom
            # may be supplied by any stronger atom in the same predicate's
            # creation scope. This preserves the weakest alternatives.
            selector.add(
                z3.Not(z3.And([z3.Or([bits[j] for j in (implies or {}).get(i, frozenset({i}))]) for i in seed]))
            )
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


def qualifier_order(predicates, assignment, choices, query):
    """Semantic implication in each predicate's own scope, not a Horn clause.

    Comparing in a clause's stronger assumptions could incorrectly discard a
    valuation needed by a later clause. Creation scopes are stable across all
    occurrences, so this ordering is safe for incremental backtracking.
    """
    formulas = []
    solver = z3.Solver()
    query.configure(solver)
    impossible = set()
    for i, (name, qualifier) in enumerate(choices):
        if monotonic() >= query.deadline:
            return {}, frozenset(impossible)
        extended = {**assignment, name: assignment[name] + [qualifier]}
        formula = z3.Or([translate(c) for c in flatten(apply_constraint(extended, predicates[name].nonempty))])
        formulas.append(formula)
        query.configure(solver)
        query.stats.solver_queries += 1
        if solver.check(formula) == z3.unsat:
            impossible.add(i)
    order = {i: {i} for i in range(len(choices))}
    for i, (name, _) in enumerate(choices):
        if i in impossible:
            continue
        for j, (other, _) in enumerate(choices):
            if i == j or name != other or j in impossible:
                continue
            if monotonic() >= query.deadline:
                return {i: frozenset(v) for i, v in order.items()}, frozenset(impossible)
            query.stats.solver_queries += 1
            query.configure(solver)
            if solver.check(formulas[j], z3.Not(formulas[i])) == z3.unsat:
                order[i].add(j)
    return {i: frozenset(v) for i, v in order.items()}, frozenset(impossible)


def semantic_minima(assignments, predicates, query):
    """Remove stronger valuations, including implications between conjunctions.

    Comparisons use each unknown's creation scope. Unknown SMT answers retain
    both alternatives; only a proved implication permits removing one.
    """
    if len(assignments) < 2:
        return assignments
    solver = z3.Solver()
    formulas = {}

    def implies(left, right):
        for name, predicate in predicates.items():
            if left[name] == right[name]:
                continue
            if monotonic() >= query.deadline:
                return False
            terms = []
            for assignment in (left, right):
                key = (
                    name,
                    tuple((n, tuple(qs)) for n, qs in sorted(assignment.items(), key=lambda item: str(item[0]))),
                )
                if key not in formulas:
                    formulas[key] = z3.Or(
                        [translate(c) for c in flatten(apply_constraint(assignment, predicate.nonempty))]
                    )
                terms.append(formulas[key])
            query.configure(solver)
            query.stats.solver_queries += 1
            if solver.check(terms[0], z3.Not(terms[1])) != z3.unsat:
                return False
        return True

    minimal = []
    try:
        for assignment in assignments:
            if any(implies(assignment, other) for other in minimal):
                continue
            minimal = [other for other in minimal if not implies(other, assignment)]
            minimal.append(assignment)
    except (AssertionError, KeyError, TypeError, ValueError, NotImplementedError, z3.Z3Exception):
        return assignments
    return minimal


def weakest_assignments(
    constraints: tuple[Constraint, ...],
    predicates: dict[Name, Predicate],
    initial: list[Assignment],
    query: SMTQuery,
    *,
    max_checks: int | None = None,
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
        if max_checks is not None and len(visited) > max_checks:
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

                try:
                    oracle = StrengtheningOracle(frozen, assignment, choices, query)
                    order, impossible = qualifier_order(predicates, assignment, choices, query)
                    subsets, status = minimal_subsets(
                        len(choices), oracle, max_checks=max_checks, implies=order, impossible=impossible
                    )
                except (AssertionError, KeyError, TypeError, ValueError, NotImplementedError, z3.Z3Exception):
                    subsets, status = [], Status.UNSUPPORTED
                if status != Status.VALID:
                    incomplete = status
                todo.extend(strengthen(indices) for indices in subsets if indices)
                break
            else:
                solutions.append(assignment)
    return Solutions(
        semantic_minima(solutions, predicates, query), incomplete or (Status.VALID if solutions else Status.EXHAUSTED)
    )
