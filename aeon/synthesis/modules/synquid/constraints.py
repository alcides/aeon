"""Forkable synthesis constraints, contextual witnesses and liquid unknowns."""

from __future__ import annotations

from dataclasses import dataclass, field, replace

from aeon.core.instantiation import type_substitution
from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidTerm, LiquidVar
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import (
    AbstractionType,
    ExistentialType,
    LiquidHornApplication,
    RefinedType,
    Type,
    TypeConstructor,
    TypeVar,
    t_bool,
)
from aeon.synthesis.modules.synquid.solver import (
    Predicate,
    SearchStats,
    SMTQuery,
    Status,
    weakest_assignments,
)
from aeon.typechecking.context import TypingContext
from aeon.typechecking.entailment import entailment_context
from aeon.typechecking.liquid import liquid_admissible
from aeon.utils.name import Name, fresh_counter
from aeon.verification.horn import (
    Assignment,
    apply_constraint,
    apply_liquid,
    build_qualifier_candidates,
    build_possible_assignment,
)
from aeon.verification.sub import sub
from aeon.verification.vcs import Constraint, LiquidConstraint


def fresh_name(label: str) -> Name:
    return Name(f"_sq_{label}", fresh_counter.fresh())


def negate(term: LiquidTerm) -> LiquidTerm:
    return LiquidApp(Name("!", 0), [term])


def map_refinements(ty: Type, assignment: Assignment) -> Type:
    if isinstance(ty, RefinedType):
        base = map_refinements(ty.type, assignment)
        assert isinstance(base, (TypeConstructor, TypeVar))
        return RefinedType(ty.name, base, apply_liquid(assignment, ty.refinement))
    if isinstance(ty, TypeConstructor):
        return TypeConstructor(ty.name, [map_refinements(a, assignment) for a in ty.args])
    if isinstance(ty, AbstractionType):
        return AbstractionType(
            ty.var_name,
            map_refinements(ty.var_type, assignment),
            map_refinements(ty.type, assignment),
            multiplicity=ty.multiplicity,
        )
    if isinstance(ty, ExistentialType):
        return ExistentialType(
            tuple((n, map_refinements(t, assignment)) for n, t in ty.binders), map_refinements(ty.body, assignment)
        )
    return ty


@dataclass
class ConstraintState:
    context: TypingContext
    constraints: tuple[Constraint, ...] = ()
    predicates: dict[Name, Predicate] = field(default_factory=dict)
    type_assignments: dict[Name, Type] = field(default_factory=dict)
    type_unknowns: frozenset[Name] = frozenset()
    assignments: list[Assignment] = field(default_factory=lambda: [{}])
    stats: SearchStats = field(default_factory=SearchStats)
    timeout_ms: int = 100
    deadline: float = float("inf")
    max_checks: int = 256
    status: Status = Status.VALID
    # Unresolved result VCs are recorded separately until their formals exist.
    pending: tuple[Constraint, ...] = ()

    def fork(self, context: TypingContext | None = None) -> ConstraintState:
        return replace(
            self,
            context=self.context if context is None else context,
            predicates=dict(self.predicates),
            type_assignments=dict(self.type_assignments),
            assignments=[{n: list(qs) for n, qs in a.items()} for a in self.assignments],
        )

    @property
    def query(self) -> SMTQuery:
        return SMTQuery(self.timeout_ms, self.stats, self.deadline)

    def lift(self, constraint: Constraint) -> Constraint:
        return entailment_context(self.context, constraint)

    def assume(self, condition: LiquidTerm) -> ConstraintState:
        child = self.fork()
        n = fresh_name("path")
        child.context = child.context.with_var(n, RefinedType(n, t_bool, condition))
        return child

    def bind(self, name: Name, ty: Type) -> None:
        if isinstance(ty, ExistentialType):
            for n, t in ty.binders:
                self.context = self.context.with_var(n, t)
            ty = ty.body
        self.context = self.context.with_var(name, ty)

    def fresh_predicate(self, ctx: TypingContext, qualifiers: frozenset[LiquidTerm]) -> LiquidHornApplication:
        args: list[tuple[LiquidTerm, TypeConstructor | TypeVar]] = [
            (LiquidVar(n), base)
            for n, ty in ctx.vars()
            if (base := liquid_admissible(ty.type if isinstance(ty, RefinedType) else ty)) is not None
        ]
        # Fresh scopes contain no repeated core names. Qualifiers are checked
        # against these exact sorts before entering the finite vocabulary.
        hole = LiquidHornApplication(fresh_name("k"), args)
        candidates = tuple(sorted(build_qualifier_candidates(ctx, hole, qualifiers), key=repr))
        nonempty = entailment_context(ctx, LiquidConstraint(negate(hole)))
        self.predicates[hole.name] = Predicate(hole, candidates, nonempty)
        for assignment in self.assignments:
            assignment[hole.name] = []
        return hole

    def refinement_parameter(self, sort: Type) -> LiquidHornApplication:
        """A declared (possibly n-ary) abstract refinement has explicit slots."""
        from aeon.core.substitutions import predicate_domains

        args: list[tuple[LiquidTerm, TypeConstructor | TypeVar]] = []
        context = self.context
        for domain in predicate_domains(sort):
            domain = domain.type if isinstance(domain, RefinedType) else domain
            if not isinstance(domain, (TypeConstructor, TypeVar)):
                raise NotImplementedError("Higher-order refinement parameter")
            n = fresh_name("predicate_arg")
            context = context.with_var(n, domain)
            args.append((LiquidVar(n), domain))
        hole = LiquidHornApplication(fresh_name("predicate"), args)
        qualifiers = tuple(sorted(build_possible_assignment(hole, self.context), key=repr))
        self.predicates[hole.name] = Predicate(
            hole, qualifiers, entailment_context(context, LiquidConstraint(negate(hole)))
        )
        for assignment in self.assignments:
            assignment[hole.name] = []
        return hole

    def fresh_type(self, shape: Type, qualifiers: frozenset[LiquidTerm]) -> Type:
        """Fresh liquid instantiation at a goal-anchored shape (VAR∀)."""
        binder = fresh_name("value")
        if isinstance(shape, RefinedType):
            from aeon.typechecking.qualifiers import extract_qualifier_atoms

            # Include the exact requirement, with its value binder aligned.
            ref = substitution_in_liquid(shape.refinement, LiquidVar(binder), shape.name)
            qualifiers = qualifiers | extract_qualifier_atoms(TypingContext(), RefinedType(binder, shape.type, ref))
            shape = shape.type
        if isinstance(shape, TypeConstructor):
            base: TypeConstructor | TypeVar = TypeConstructor(
                shape.name, [self.fresh_type(a, qualifiers) for a in shape.args]
            )
        elif isinstance(shape, TypeVar):
            base = shape
        else:
            # Higher-kinded/function instantiations stay opaque to liquid SMT.
            return shape
        hole = self.fresh_predicate(self.context.with_var(binder, base), qualifiers)
        return RefinedType(binder, base, hole)

    def add(self, constraint: Constraint, *, lifted: bool = False) -> None:
        self.constraints += (constraint if lifted else self.lift(constraint),)

    def subtype(self, actual: Type, expected: Type) -> None:
        self.add(sub(self.context, actual, expected))

    def solve(self) -> Status:
        if not self.predicates:
            for constraint in self.constraints:
                result = self.query.valid(constraint)
                if result != Status.VALID:
                    self.status = self.stats.record(result)
                    return self.status
            self.status = Status.VALID
        else:
            solutions = weakest_assignments(
                self.constraints, self.predicates, self.assignments, self.query, max_checks=self.max_checks
            )
            self.status = solutions.status
            # An interrupted solve must not replace unexamined possibilities
            # with only the successful prefix. Retain the old seeds to retry.
            if solutions.status in (Status.VALID, Status.EXHAUSTED):
                self.assignments = solutions.assignments
        return self.stats.record(self.status)

    def inhabited(self, context: TypingContext | None = None) -> Status:
        """INVALID denotes a proved nonempty context; VALID denotes empty."""
        constraint = entailment_context(context or self.context, LiquidConstraint(LiquidLiteralBool(False)))
        results = [self.query.valid(apply_constraint(a, constraint)) for a in self.assignments]
        if Status.INVALID in results:
            return Status.INVALID
        if results and all(r == Status.VALID for r in results):
            return Status.VALID
        return Status.UNKNOWN

    def resolve(self, ty: Type) -> Type:
        for name, replacement in self.type_assignments.items():
            ty = type_substitution(ty, name, replacement)
        return ty

    def unresolved(self, ty: Type) -> set[Name]:
        ty = self.resolve(ty)
        if isinstance(ty, TypeVar):
            return {ty.name} & self.type_unknowns
        if isinstance(ty, RefinedType):
            return self.unresolved(ty.type)
        if isinstance(ty, TypeConstructor):
            return set().union(*(self.unresolved(t) for t in ty.args))
        if isinstance(ty, AbstractionType):
            return self.unresolved(ty.var_type) | self.unresolved(ty.type)
        return set()

    def materialize(self, ty: Type, assignment: Assignment | None = None) -> Type:
        ty = self.resolve(ty)
        return map_refinements(ty, assignment if assignment is not None else self.assignments[0])
