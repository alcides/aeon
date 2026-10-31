"""Forkable synthesis constraints, contextual witnesses and liquid unknowns."""

from __future__ import annotations

from dataclasses import dataclass, field, replace

from aeon.core.instantiation import type_substitution
from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidTerm, LiquidVar
from aeon.core.substitutions import substitution_in_liquid, substitution_in_type
from aeon.core.terms import Var
from aeon.core.types import (
    AbstractionType,
    ExistentialType,
    LiquidHornApplication,
    RefinedType,
    Type,
    TypeConstructor,
    TypeVar,
    t_bool,
    Kind,
    TypePolymorphism,
    RefinementPolymorphism,
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
    if isinstance(ty, TypePolymorphism):
        return TypePolymorphism(ty.name, ty.kind, map_refinements(ty.body, assignment))
    if isinstance(ty, RefinementPolymorphism):
        return RefinementPolymorphism(
            ty.name, map_refinements(ty.sort, assignment), map_refinements(ty.body, assignment)
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
    timeout_ms: int = 0
    deadline: float = float("inf")
    max_checks: int | None = None
    status: Status = Status.VALID
    # Unresolved result VCs are recorded separately until their formals exist.
    pending: tuple[Constraint, ...] = ()
    match_depth: int = 0
    matched: frozenset[Name] = frozenset()
    type_obligations: tuple[tuple[TypingContext, Type, Type], ...] = ()

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
        from aeon.typechecking.liquid import lower_context

        return SMTQuery(self.timeout_ms, self.stats, self.deadline, lower_context(self.resolve_context(self.context)))

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
            qualifiers = qualifiers | extract_qualifier_atoms(
                TypingContext(), RefinedType(binder, shape.type, ref), max_atoms=None
            )
            shape = shape.type
        if isinstance(shape, TypeConstructor):
            base: TypeConstructor | TypeVar = TypeConstructor(
                shape.name, [self.fresh_type(a, qualifiers) for a in shape.args]
            )
        elif isinstance(shape, TypeVar):
            if shape.name in self.type_unknowns:
                return self.fresh_variable()
            base = shape
        elif isinstance(shape, AbstractionType):
            domain = self.fresh_type(shape.var_type, qualifiers)
            child = self.fork(self.context.with_var(shape.var_name, domain))
            result = child.fresh_type(shape.type, qualifiers)
            self.predicates = child.predicates
            self.assignments = child.assignments
            self.type_unknowns = child.type_unknowns
            return AbstractionType(shape.var_name, domain, result, multiplicity=shape.multiplicity)
        else:
            # Higher-kinded/function instantiations stay opaque to liquid SMT.
            return shape
        hole = self.fresh_predicate(self.context.with_var(binder, base), qualifiers)
        return RefinedType(binder, base, hole)

    def add(self, constraint: Constraint, *, lifted: bool = False) -> None:
        self.constraints += (constraint if lifted else self.lift(constraint),)

    def subtype(self, actual: Type, expected: Type) -> None:
        self.type_obligations += ((self.context, actual, expected),)

    def fresh_variable(self, kind: Kind = Kind.BASE) -> TypeVar:
        variable = TypeVar(fresh_name("type"))
        self.type_unknowns |= {variable.name}
        self.context = self.context.with_typevar(variable.name, kind)
        return variable

    def unify_shapes(self, left: Type, right: Type, qualifiers=frozenset()) -> None:
        """Figure 6: interleave shape discovery with refinement constraints.

        Two free variables stay related by the pending subtype obligation;
        they are not identified (their refinements can differ). An assignment
        copies a structured shape with fresh inner unknowns and predicates.
        """
        left, right = self.resolve(left), self.resolve(right)
        if isinstance(left, ExistentialType):
            left = left.body
        if isinstance(right, ExistentialType):
            right = right.body
        lb = left.type if isinstance(left, RefinedType) else left
        rb = right.type if isinstance(right, RefinedType) else right
        lu = isinstance(lb, TypeVar) and lb.name in self.type_unknowns
        ru = isinstance(rb, TypeVar) and rb.name in self.type_unknowns
        if lu and ru:
            return
        if lu or ru:
            variable, shape = (lb, right) if lu else (rb, left)
            assert isinstance(variable, TypeVar)
            if variable.name in self.unresolved(shape):
                raise ValueError("Infinite type in synthesis unification")
            from aeon.typechecking.qualifiers import extract_qualifier_atoms

            self.type_assignments[variable.name] = self.fresh_type(
                shape, qualifiers | extract_qualifier_atoms(self.context, shape, max_atoms=None)
            )
            # Fresh copies of nested free variables retain their subtype
            # relationship through the caller's queued obligation.
            return
        if isinstance(lb, TypeConstructor) and isinstance(rb, TypeConstructor):
            if lb.name != rb.name or len(lb.args) != len(rb.args):
                raise ValueError("Incompatible constructor shapes")
            for a, b in zip(lb.args, rb.args):
                self.unify_shapes(a, b, qualifiers)
        elif isinstance(lb, AbstractionType) and isinstance(rb, AbstractionType):
            self.unify_shapes(rb.var_type, lb.var_type, qualifiers)
            self.unify_shapes(lb.type, substitution_in_type(rb.type, Var(lb.var_name), rb.var_name), qualifiers)
        elif lb != rb:
            raise ValueError("Incompatible type shapes")

    def solve(self) -> Status:
        try:
            while True:
                count = len(self.type_assignments)
                for _, left, right in self.type_obligations:
                    self.unify_shapes(left, right)
                if len(self.type_assignments) == count:
                    break
            typed = []
            for context, left, right in self.type_obligations:
                left, right = self.resolve(left), self.resolve(right)
                typed.extend(self.subtype_constraints(self.resolve_context(context), left, right))
            constraints = tuple(self.resolve_constraint(c) for c in self.constraints) + tuple(typed)
        except ValueError:
            self.status = self.stats.record(Status.INVALID)
            return self.status
        if not self.predicates:
            for constraint in constraints:
                result = self.query.valid(constraint)
                if result != Status.VALID:
                    self.status = self.stats.record(result)
                    return self.status
            self.status = Status.VALID
        else:
            solutions = weakest_assignments(
                constraints,
                {
                    n: Predicate(self.resolve_liquid(p.occurrence), p.qualifiers, self.resolve_constraint(p.nonempty))
                    for n, p in self.predicates.items()
                },
                self.assignments,
                self.query,
                max_checks=self.max_checks,
            )
            self.status = solutions.status
            # An interrupted solve must not replace unexamined possibilities
            # with only the successful prefix. Retain the old seeds to retry.
            if solutions.status in (Status.VALID, Status.EXHAUSTED):
                self.assignments = solutions.assignments
        return self.stats.record(self.status)

    def subtype_constraints(self, context, left, right):
        """Solve outer refinements before nested free shapes are determined."""
        from aeon.core.types import extract_parts
        from aeon.synthesis.modules.synquid.round_trip import erase

        if not self.unresolved(left) and not self.unresolved(right):
            return [entailment_context(context, sub(context, left, right))]
        if isinstance(left, AbstractionType) and isinstance(right, AbstractionType):
            binder = fresh_name("subtype_arg")
            return self.subtype_constraints(context, right.var_type, left.var_type) + self.subtype_constraints(
                context.with_var(binder, right.var_type),
                substitution_in_type(left.type, Var(binder), left.var_name),
                substitution_in_type(right.type, Var(binder), right.var_name),
            )
        ln, lb, lp = extract_parts(left)
        rn, rb, rp = extract_parts(right)
        if isinstance(lb, TypeConstructor) and isinstance(rb, TypeConstructor):
            # Shape unification has already checked equal heads and arities.
            common = erase(lb)
            constraints = [
                entailment_context(context, sub(context, RefinedType(ln, common, lp), RefinedType(rn, common, rp)))
            ]
            for a, b in zip(lb.args, rb.args):
                constraints.extend(self.subtype_constraints(context, a, b))
            return constraints
        return []

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
        if isinstance(ty, ExistentialType):
            return ExistentialType(tuple((n, self.resolve(t)) for n, t in ty.binders), self.resolve(ty.body))
        # Assignments may form a dependency chain created by later arguments.
        for _ in range(len(self.type_assignments) + 1):
            previous = ty
            for name, replacement in self.type_assignments.items():
                ty = type_substitution(ty, name, replacement)
            if ty == previous:
                break
        return ty

    def resolve_liquid(self, term):
        from aeon.synthesis.modules.synquid.round_trip import erase

        if isinstance(term, LiquidHornApplication):
            return LiquidHornApplication(
                term.name, [(self.resolve_liquid(a), erase(self.resolve(t))) for a, t in term.argtypes]
            )
        if isinstance(term, LiquidApp):
            return LiquidApp(term.fun, [self.resolve_liquid(a) for a in term.args])
        return term

    def resolve_constraint(self, constraint):
        from aeon.verification.vcs import (
            Implication,
            Conjunction,
            UninterpretedFunctionDeclaration,
            ReflectedFunctionDeclaration,
        )

        if isinstance(constraint, LiquidConstraint):
            return LiquidConstraint(self.resolve_liquid(constraint.expr))
        if isinstance(constraint, Conjunction):
            return Conjunction(self.resolve_constraint(constraint.c1), self.resolve_constraint(constraint.c2))
        if isinstance(constraint, Implication):
            from aeon.synthesis.modules.synquid.round_trip import erase

            return Implication(
                constraint.name,
                erase(self.resolve_sort(constraint.base)),
                self.resolve_liquid(constraint.pred),
                self.resolve_constraint(constraint.seq),
            )
        if isinstance(constraint, (UninterpretedFunctionDeclaration, ReflectedFunctionDeclaration)):
            return replace(
                constraint, type=self.resolve_sort(constraint.type), seq=self.resolve_constraint(constraint.seq)
            )
        return constraint

    def resolve_sort(self, ty):
        """Also resolve unknowns already lowered to nullary VC constructors."""
        if isinstance(ty, TypeConstructor):
            if not ty.args and ty.name in self.type_unknowns:
                return self.resolve(TypeVar(ty.name))
            return TypeConstructor(ty.name, [self.resolve_sort(a) for a in ty.args])
        if isinstance(ty, AbstractionType):
            return AbstractionType(
                ty.var_name, self.resolve_sort(ty.var_type), self.resolve_sort(ty.type), multiplicity=ty.multiplicity
            )
        if isinstance(ty, RefinedType):
            return self.resolve(ty)
        return self.resolve(ty)

    def finalize(self):
        """Close residual free/free and phantom variables at an E-term leaf.

        Unconstrained shapes may use any inhabited base sort. Preserve fresh
        refinements so the pending subtype relations still have to be solved.
        """
        from aeon.core.types import t_int

        for name in sorted(self.type_unknowns, key=str):
            if name not in self.type_assignments:
                self.type_assignments[name] = self.fresh_type(t_int, frozenset())
        return self.solve()

    def resolve_context(self, context):
        entries = [replace(e, type=self.resolve(e.type)) if hasattr(e, "type") else e for e in context.entries]
        return TypingContext(entries, trusted_names=context.trusted_names)

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
        if isinstance(ty, ExistentialType):
            return self.unresolved(ty.body) | set().union(*(self.unresolved(t) for _, t in ty.binders))
        return set()

    def materialize(self, ty: Type, assignment: Assignment | None = None) -> Type:
        ty = self.resolve(ty)
        return map_refinements(ty, assignment if assignment is not None else self.assignments[0])
