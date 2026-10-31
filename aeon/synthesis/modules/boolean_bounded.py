"""Finite Boolean CNF synthesis with shared compiler VCs and SAT-based CEGIS.

Selector bits are the only candidate unknowns. Counterexamples constrain the
whole relation, never arbitrarily chosen output labels. This is a feasibility
solver: it neither widens K nor claims an optimum for secondary objectives.
"""

from __future__ import annotations

from dataclasses import dataclass, fields, is_dataclass
from time import monotonic
from typing import Callable

import z3

from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt, LiquidTerm, LiquidVar
from aeon.core.multiplicity import MOmega
from aeon.core.terms import Application, Let, Literal, Rec, Term, Var
from aeon.core.types import AbstractionType, Type, t_bool
from aeon.decorators.api import Metadata
from aeon.synthesis.api import SynthesisNotSuccessful, TimeoutInEvaluationException, UnsupportedSynthesisGoal
from aeon.synthesis.bounded_cnf import CNFResourceLimit, base, bounds, normalize
from aeon.synthesis.joint import HoleSpec, JointCandidate
from aeon.synthesis.solver_problem import ConstraintSynthesizer, SolverHole, SolverProblem
from aeon.synthesis.uis.api import SynthesisUI
from aeon.utils.name import Name


class BoundedBooleanFailure(SynthesisNotSuccessful):
    def __init__(self, category: str, message: str):
        self.category = category
        super().__init__(f"boolean_bounded [{category}]: {message}")


@dataclass
class BooleanReport:
    status: str = "running"
    iterations: int = 0
    counterexamples: int = 0
    selectors: int = 0
    elapsed: float = 0.0


def _boolean_signature(ty: Type) -> None:
    while isinstance(ty, AbstractionType):
        if base(ty.var_type) != t_bool or ty.multiplicity is not MOmega:
            raise UnsupportedSynthesisGoal("boolean_bounded requires unrestricted, first-order Boolean inputs")
        ty = ty.type
    if base(ty) != t_bool:
        raise UnsupportedSynthesisGoal("boolean_bounded requires a Boolean result without unresolved polymorphism")


def _nodes(term: Term):
    """Walk core children without descending into types or source locations."""
    yield term
    assert is_dataclass(term)
    for field in fields(term):
        child = getattr(term, field.name)
        if isinstance(child, Term):
            yield from _nodes(child)


def _operator(op: str, *args: Term) -> Term:
    result: Term = Var(Name(op, 0))
    for arg in args:
        result = Application(result, arg)
    return result


def _combine(op: str, terms: list[Term], identity: bool) -> Term:
    # Balanced trees avoid a linear Python/compiler recursion depth in K or n.
    if not terms:
        return Literal(identity, t_bool)
    if len(terms) == 1:
        return terms[0]
    mid = len(terms) // 2
    return _operator(op, _combine(op, terms[:mid], identity), _combine(op, terms[mid:], identity))


class _Template:
    def __init__(self, schema: SolverHole, k: int, index: int):
        self.schema = schema
        self.k = k
        self.enabled = [z3.Bool(f"s{index}_e{c}") for c in range(k)]
        self.positive = [[z3.Bool(f"s{index}_p{c}_{i}") for i in range(len(schema.params))] for c in range(k)]
        self.negative = [[z3.Bool(f"s{index}_n{c}_{i}") for i in range(len(schema.params))] for c in range(k)]
        self.selectors = self.enabled + [s for row in self.positive + self.negative for s in row]

    def constraints(self):
        # Tautologies may always be replaced by disabled slots (an at-most bound).
        return [z3.Not(z3.And(p, n)) for ps, ns in zip(self.positive, self.negative) for p, n in zip(ps, ns)]

    def apply(self, args: list[z3.BoolRef]) -> z3.BoolRef:
        if len(args) != len(self.schema.params):
            raise UnsupportedSynthesisGoal("Boolean unknown applied with the wrong arity")
        return z3.And(
            [
                z3.Or(
                    z3.Not(e),
                    *[z3.And(p, x) for p, x in zip(ps, args)],
                    *[z3.And(n, z3.Not(x)) for n, x in zip(ns, args)],
                )
                for e, ps, ns in zip(self.enabled, self.positive, self.negative)
            ]
        )

    def extract(self, model: z3.ModelRef) -> Term:
        def selected(bit):
            return z3.is_true(model.eval(bit, model_completion=True))

        clauses = []
        for e, ps, ns in zip(self.enabled, self.positive, self.negative):
            if selected(e):
                literals: list[Term] = []
                for (name, _), p, n in zip(self.schema.params, ps, ns):
                    if selected(p):
                        literals.append(Var(name))
                    if selected(n):
                        literals.append(_operator("!", Var(name)))
                clauses.append(_combine("||", literals, False))
        body = _combine("&&", clauses, True)
        if len(normalize(body, {n for n, _ in self.schema.params})) > self.k:
            raise BoundedBooleanFailure("validation_error", "extracted CNF exceeds its bound")
        return self.schema.wrap(body)


class BooleanBoundedSynthesizer(ConstraintSynthesizer):
    requires_joint_obligations = True
    lexical_inputs_only = True

    def __init__(self, seed: int = 0, *, max_selectors: int = 100_000, max_nodes: int = 100_000):
        self.seed = seed
        self.max_selectors = max_selectors
        self.max_nodes = max_nodes
        self.report = BooleanReport()

    def check_source(self, program: Term, holes: tuple[HoleSpec, ...], metadata: Metadata) -> None:
        self.report = BooleanReport()
        try:
            self._check_source(program, holes, metadata)
        except UnsupportedSynthesisGoal:
            self.report.status = "unsupported"
            raise
        except RecursionError as exc:
            self.report.status = "resource_limit"
            raise BoundedBooleanFailure("resource_limit", "Boolean source recursion limit exceeded") from exc

    def _check_source(self, program: Term, holes: tuple[HoleSpec, ...], metadata: Metadata) -> None:
        limits = bounds(metadata)
        owners = [h.function for h in holes]
        if len(set(owners)) != len(owners):
            raise UnsupportedSynthesisGoal("boolean_bounded supports one hole per annotated definition")
        if any(owner not in limits for owner in owners):
            raise UnsupportedSynthesisGoal("every Boolean synthesis target needs @bounded_cnf(K)")
        for hole in holes:
            _boolean_signature(hole.type)
        definitions = {}
        while isinstance(program, (Let, Rec)):
            definitions[program.var_name] = program
            program = program.body
        roots = set(owners) | {n for n, e in metadata.items() if isinstance(e, dict) and "property" in e}
        roots |= {ex.function for e in metadata.values() if isinstance(e, dict) for ex in e.get("examples", [])}
        visiting: set[Name] = set()
        visited: set[Name] = set()

        def inspect(name):
            if name in visiting:
                raise UnsupportedSynthesisGoal("boolean_bounded does not support recursive specifications")
            if name in visited or name not in definitions:
                return
            visiting.add(name)
            definition = definitions[name]
            if not isinstance(definition, Rec):
                raise UnsupportedSynthesisGoal("Boolean specifications need typed definitions")
            _boolean_signature(definition.var_type)
            for node in _nodes(definition.var_value):
                if isinstance(node, Rec):
                    raise UnsupportedSynthesisGoal("boolean_bounded does not support local recursion")
                if isinstance(node, Let) and node.multiplicity is not MOmega:
                    raise UnsupportedSynthesisGoal("boolean_bounded requires unrestricted local bindings")
                if isinstance(node, Var):
                    if node.name.name == "native":
                        raise UnsupportedSynthesisGoal("boolean_bounded cannot translate native specifications")
                    inspect(node.name)
            visiting.remove(name)
            visited.add(name)

        for name in sorted(roots, key=str):
            inspect(name)

    def synthesize_joint(
        self,
        holes: tuple[HoleSpec, ...],
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        fun_name: Name,
        metadata: Metadata,
        budget: float = 60,
        ui: SynthesisUI = SynthesisUI(),
    ) -> JointCandidate:
        start = monotonic()
        deadline = start + max(0.0, budget)
        self.report = BooleanReport()

        def remaining():
            value = deadline - monotonic()
            if value <= 0:
                raise BoundedBooleanFailure("timeout", "wall-clock budget exhausted")
            return value

        def check(solver):
            solver.set(timeout=max(1, int(remaining() * 1000)))
            result = solver.check()
            remaining()
            if result == z3.unknown:
                reason = solver.reason_unknown()
                category = "timeout" if "timeout" in reason or "canceled" in reason else "unknown"
                raise BoundedBooleanFailure(category, reason)
            return result

        try:
            remaining()
            entry = metadata.get(fun_name, {})
            problem = entry.get("solver_problem")
            if not isinstance(problem, SolverProblem) or tuple(h.name for h in holes) != tuple(
                h.name for h in problem.holes
            ):
                raise UnsupportedSynthesisGoal("boolean_bounded requires the shared compiler solver problem")
            limits = bounds(metadata)
            templates = {}
            for index, (hole, schema) in enumerate(zip(holes, problem.holes)):
                k = limits.get(hole.function)
                if type(k) is not int or k < 0:
                    raise UnsupportedSynthesisGoal("every Boolean synthesis target needs @bounded_cnf(K)")
                _boolean_signature(hole.type)
                if schema.base != t_bool or any(ty != t_bool for _, ty in schema.params):
                    raise UnsupportedSynthesisGoal("boolean_bounded supports only Boolean unknowns and lexical inputs")
                self.report.selectors += k * (1 + 2 * len(schema.params))
                if self.report.selectors > self.max_selectors:
                    raise BoundedBooleanFailure("resource_limit", "CNF selector limit exceeded")
                templates[schema.symbol] = _Template(schema, k, index)
                remaining()
            selectors = [s for t in templates.values() for s in t.selectors]
            candidate_solver, verifier = z3.Solver(), z3.Solver()
            for solver in (candidate_solver, verifier):
                solver.set(random_seed=self.seed % (2**32))
            for template in templates.values():
                candidate_solver.add(template.constraints())
            nodes = 0

            def translate(term: LiquidTerm, variables: dict[Name, z3.BoolRef]) -> z3.BoolRef:
                nonlocal nodes
                nodes += 1
                if nodes > self.max_nodes:
                    raise BoundedBooleanFailure("resource_limit", "Boolean obligation size limit exceeded")
                remaining()
                if isinstance(term, LiquidLiteralBool):
                    return z3.BoolVal(term.value)
                if isinstance(term, LiquidVar) and term.name in variables:
                    return variables[term.name]
                if isinstance(term, LiquidApp):
                    if term.fun in templates:
                        template = templates[term.fun]
                        nodes += template.k * (1 + 4 * len(template.schema.params))
                        if nodes > self.max_nodes:
                            raise BoundedBooleanFailure(
                                "resource_limit", "expanded Boolean template size limit exceeded"
                            )
                        if template.schema.dummy:
                            if term.args != [LiquidLiteralInt(0)]:
                                raise UnsupportedSynthesisGoal("invalid nullary unknown transport")
                            return template.apply([])
                        return template.apply([translate(a, variables) for a in term.args])
                    args = [translate(a, variables) for a in term.args]
                    op = term.fun.name if term.fun.id == 0 else None
                    if op == "!" and len(args) == 1:
                        return z3.Not(args[0])
                    if len(args) == 2:
                        a, b = args
                        if op == "&&":
                            return z3.And(a, b)
                        if op == "||":
                            return z3.Or(a, b)
                        if op == "-->":
                            return z3.Implies(a, b)
                        if op == "==":
                            return a == b
                        if op == "!=":
                            return a != b
                    if op == "ite" and len(args) == 3:
                        return z3.If(*args)
                raise UnsupportedSynthesisGoal(f"boolean_bounded cannot translate Boolean predicate {term}")

            obligations = []
            for index, clause in enumerate(problem.clauses):
                if any(ty != t_bool for _, ty in clause.variables):
                    raise UnsupportedSynthesisGoal("boolean_bounded requires Boolean verification variables")
                variables = {n: z3.Bool(f"v{index}_{i}") for i, (n, _) in enumerate(clause.variables)}
                relation = z3.Implies(translate(clause.premise, variables), translate(clause.conclusion, variables))
                obligations.append((tuple(variables.values()), relation))
            while True:
                self.report.iterations += 1
                if check(candidate_solver) == z3.unsat:
                    raise BoundedBooleanFailure(
                        "bounded_unsat", "no solution within the stated CNF bounds and supported grammar"
                    )
                model = candidate_solver.model()
                frozen = [(s, model.eval(s, model_completion=True)) for s in selectors]
                violations = [z3.Not(z3.substitute(relation, frozen)) for _, relation in obligations]
                verifier.push()
                verifier.add(z3.Or(violations))
                status = check(verifier)
                if status == z3.unsat:
                    verifier.pop()
                    candidate = JointCandidate(tuple(t.extract(model) for t in templates.values()))
                    remaining()
                    if not validate(candidate):
                        raise BoundedBooleanFailure(
                            "validation_error", "solver candidate failed full Aeon/CNF validation"
                        )
                    remaining()
                    fitness = evaluate(candidate) if entry.get("goals") else []
                    remaining()
                    self.report.status = "solved"
                    ui.register(candidate, fitness, monotonic() - start, True)
                    return candidate
                counterexample = verifier.model()
                index = next(
                    i
                    for i, violation in enumerate(violations)
                    if z3.is_true(counterexample.eval(violation, model_completion=True))
                )
                inputs, relation = obligations[index]
                instance = z3.substitute(relation, [(v, counterexample.eval(v, model_completion=True)) for v in inputs])
                verifier.pop()
                candidate_solver.add(instance)
                self.report.counterexamples += 1
        except BoundedBooleanFailure as exc:
            self.report.status = exc.category
            raise
        except TimeoutInEvaluationException as exc:
            self.report.status = "timeout"
            raise BoundedBooleanFailure("timeout", "objective evaluation timed out") from exc
        except UnsupportedSynthesisGoal:
            self.report.status = "unsupported"
            raise
        except (RecursionError, CNFResourceLimit) as exc:
            self.report.status = "resource_limit"
            raise BoundedBooleanFailure("resource_limit", "Boolean syntax normalization limit exceeded") from exc
        except Exception as exc:
            self.report.status = "validation_error"
            raise BoundedBooleanFailure("validation_error", f"{type(exc).__name__}: {exc}") from exc
        finally:
            self.report.elapsed = monotonic() - start
