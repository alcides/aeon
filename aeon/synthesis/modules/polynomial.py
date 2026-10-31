"""Bounded polynomial synthesis by existential algebraic certificates.

For each compiler obligation ``g >= 0, h = 0 => p >= 0``, match coefficients
in ``p = sum(lambda_alpha * g**alpha) + sigma_0 + sum(sigma_i*g_i)
+ sum(q_j*h_j)``. Lambdas are nonnegative, sigmas are sums of polynomial
squares, and q's are unrestricted polynomials. No universal input variables
are sent to the synthesis solver. This is a bounded Handelman/Putinar-style
subset of Goharshady et al., https://arxiv.org/abs/2209.03602, not a complete
implementation of that paper's imperative language or completeness result.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations_with_replacement
from math import comb, isfinite
import os
import time

import z3

from aeon.core.liquid import (
    LiquidApp,
    LiquidLiteralBool,
    LiquidLiteralFloat,
    LiquidLiteralInt,
    LiquidTerm,
    LiquidVar,
    liquid_free_vars,
)
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.terms import Term, Var
from aeon.core.types import t_float, t_int
from aeon.synthesis.api import SynthesisNotSuccessful, UnsupportedSynthesisGoal
from aeon.synthesis.joint import JointCandidate
from aeon.synthesis.modules.sygus.solver import _apply_op, _num_literal
from aeon.synthesis.solver_problem import ConstraintSynthesizer, SolverHole, SolverProblem
from aeon.synthesis.uis.api import SynthesisUI
from aeon.utils.name import Name

Monomial = tuple[int, ...]
Polynomial = dict[Monomial, z3.ArithRef]


@dataclass(frozen=True)
class PolynomialConfig:
    degree: int = 2
    certificate_degree: int = 2
    sos_degree: int = 1
    max_terms: int = 4096
    max_unknowns: int = 10000
    max_branches: int = 64

    def __post_init__(self):
        if min(self.degree, self.certificate_degree, self.sos_degree) < 0:
            raise UnsupportedSynthesisGoal("Polynomial degrees must be nonnegative")
        if min(self.max_terms, self.max_unknowns, self.max_branches) < 1:
            raise UnsupportedSynthesisGoal("Polynomial size limits must be positive")

    @classmethod
    def from_env(cls):
        try:
            return cls(
                degree=int(os.environ.get("AEON_POLYNOMIAL_DEGREE", "2")),
                certificate_degree=int(os.environ.get("AEON_POLYNOMIAL_CERTIFICATE_DEGREE", "2")),
                sos_degree=int(os.environ.get("AEON_POLYNOMIAL_SOS_DEGREE", "1")),
            )
        except ValueError as exc:
            raise UnsupportedSynthesisGoal("Polynomial degree settings must be integers") from exc


class CertificateProblem:
    """Sparse polynomials separate universal monomials from existential coefficients."""

    def __init__(self, problem: SolverProblem, config: PolynomialConfig, deadline: float):
        self.problem = problem
        self.config = config
        self.deadline = deadline
        self.solver = z3.Solver()
        self.unknowns = 0
        self.templates: dict[Name, tuple[SolverHole, Polynomial]] = {}
        for hole in problem.holes:
            if hole.base not in (t_int, t_float) or any(base != hole.base for _, base in hole.params):
                raise UnsupportedSynthesisGoal("Polynomial holes need homogeneous Int or Float inputs and output")
            self.templates[hole.symbol] = (
                hole,
                {m: self.fresh(integer=hole.base == t_int) for m in self.monomials(len(hole.params), config.degree)},
            )

    def remaining_ms(self) -> int:
        remaining = self.deadline - time.monotonic()
        if remaining <= 0:
            raise SynthesisNotSuccessful("Polynomial synthesis exhausted its time budget")
        return max(1, int(remaining * 1000))

    def fresh(self, integer=False):
        self.remaining_ms()
        self.unknowns += 1
        if self.unknowns > self.config.max_unknowns:
            raise SynthesisNotSuccessful("Polynomial certificate exceeded its unknown-coefficient limit")
        return (z3.Int if integer else z3.Real)(f"polynomial_c{self.unknowns}")

    def monomials(self, n: int, degree: int):
        if comb(n + degree, degree) > self.config.max_terms:
            raise SynthesisNotSuccessful("Polynomial basis exceeded its monomial limit")
        for d in range(degree + 1):
            self.remaining_ms()
            for indices in combinations_with_replacement(range(n), d):
                powers = [0] * n
                for i in indices:
                    powers[i] += 1
                yield tuple(powers)

    def constant(self, n: int, value) -> Polynomial:
        return {(0,) * n: z3.RealVal(value)}

    def add(self, left: Polynomial, right: Polynomial) -> Polynomial:
        out = dict(left)
        for m, c in right.items():
            out[m] = z3.simplify(out.get(m, z3.RealVal(0)) + c)
        if len(out) > self.config.max_terms:
            raise SynthesisNotSuccessful("Polynomial expansion exceeded its monomial limit")
        return {m: c for m, c in out.items() if not z3.is_true(z3.simplify(c == 0))}

    def scale(self, p: Polynomial, c) -> Polynomial:
        return {m: z3.simplify(v * c) for m, v in p.items()}

    def multiply(self, left: Polynomial, right: Polynomial) -> Polynomial:
        if len(left) * len(right) > self.config.max_terms:
            raise SynthesisNotSuccessful("Polynomial product exceeded its expansion limit")
        out: Polynomial = {}
        self.remaining_ms()
        for a, ca in left.items():
            for b, cb in right.items():
                m = tuple(x + y for x, y in zip(a, b))
                out[m] = z3.simplify(out.get(m, z3.RealVal(0)) + ca * cb)
        return out

    def expression(self, term: LiquidTerm, variables: dict[Name, Polynomial], n: int) -> Polynomial:
        self.remaining_ms()
        if isinstance(term, (LiquidLiteralInt, LiquidLiteralFloat)):
            if isinstance(term.value, float) and not isfinite(term.value):
                raise UnsupportedSynthesisGoal("Polynomial literals must be finite")
            return self.constant(n, str(term.value))
        if isinstance(term, LiquidVar) and term.name in variables:
            return variables[term.name]
        if isinstance(term, LiquidApp):
            if term.fun in self.templates:
                hole, template = self.templates[term.fun]
                args = term.args if hole.params else []  # compiler's nullary dummy argument
                if len(args) != len(hole.params):
                    raise UnsupportedSynthesisGoal("Polynomial hole application has the wrong arity")
                values = [self.expression(a, variables, n) for a in args]
                result: Polynomial = {}
                for powers, coefficient in template.items():
                    piece = self.constant(n, 1)
                    for value, exponent in zip(values, powers):
                        for _ in range(exponent):
                            piece = self.multiply(piece, value)
                    result = self.add(result, self.scale(piece, coefficient))
                return result
            if term.fun.name in ("+", "-", "*") and len(term.args) == 2:
                left, right = (self.expression(a, variables, n) for a in term.args)
                if term.fun.name == "*":
                    return self.multiply(left, right)
                return self.add(left, self.scale(right, -1) if term.fun.name == "-" else right)
        raise UnsupportedSynthesisGoal(f"Polynomial backend cannot translate arithmetic expression {term}")

    def branches(self, term: LiquidTerm, negate=False) -> list[list[LiquidTerm]]:
        """DNF of premises; strict boundaries are conservatively closed later."""
        self.remaining_ms()
        if isinstance(term, LiquidLiteralBool):
            return [[]] if term.value != negate else []
        if isinstance(term, LiquidApp):
            op, args = term.fun.name, term.args
            if op == "!" and len(args) == 1:
                return self.branches(args[0], not negate)
            if op in ("&&", "||") and len(args) == 2:
                a, b = (self.branches(t, negate) for t in args)
                conjunction = (op == "&&") != negate
                size = len(a) * len(b) if conjunction else len(a) + len(b)
                if size > self.config.max_branches:
                    raise SynthesisNotSuccessful("Polynomial premise exceeded its branch limit")
                return [x + y for x in a for y in b] if conjunction else a + b
            inverse = {"<": ">=", "<=": ">", ">": "<=", ">=": "<", "==": "!=", "!=": "=="}
            if op in inverse and len(args) == 2:
                op = inverse[op] if negate else op
                if op == "!=":
                    return [[LiquidApp(Name(c, 0), args)] for c in ("<", ">")]
                return [[LiquidApp(Name(op, 0), args)]]
        raise UnsupportedSynthesisGoal(f"Polynomial backend cannot translate premise {term}")

    def difference(self, atom: LiquidApp, variables, n):
        a, b = (self.expression(t, variables, n) for t in atom.args)
        return self.add(a, self.scale(b, -1))

    def sos(self, n: int) -> Polynomial:
        basis = list(self.monomials(n, self.config.sos_degree))
        result: Polynomial = {}
        # A PSD Gram matrix of size m has a factorization with at most m rows.
        for _ in basis:
            square_root = {m: self.fresh() for m in basis}
            result = self.add(result, self.multiply(square_root, square_root))
        return result

    def certify(self, p: Polynomial, nonnegative: list[Polynomial], equalities: list[Polynomial], n: int, strict=False):
        certificate: Polynomial = {}
        # Handelman products include 1 (a nonnegative constant) and each g_i.
        for powers in self.monomials(len(nonnegative), self.config.certificate_degree):
            product = self.constant(n, 1)
            for g, exponent in zip(nonnegative, powers):
                for _ in range(exponent):
                    product = self.multiply(product, g)
            weight = self.fresh()
            self.solver.add(weight >= 0)
            certificate = self.add(certificate, self.scale(product, weight))
        if self.config.sos_degree:
            certificate = self.add(certificate, self.sos(n))
            for g in nonnegative:
                certificate = self.add(certificate, self.multiply(self.sos(n), g))
        for h in equalities:
            multiplier = {m: self.fresh() for m in self.monomials(n, self.config.certificate_degree)}
            certificate = self.add(certificate, self.multiply(multiplier, h))
        if strict:
            # A positive constant margin is sufficient, but not necessary on open domains.
            margin = self.fresh()
            self.solver.add(margin > 0)
            certificate = self.add(certificate, self.scale(self.constant(n, 1), margin))
        difference = self.add(p, self.scale(certificate, -1))
        self.solver.add(*(coefficient == 0 for coefficient in difference.values()))

    def conclusion(self, term, nonnegative, equalities, variables, n):
        if isinstance(term, LiquidLiteralBool):
            if not term.value:
                self.certify(self.constant(n, -1), nonnegative, equalities, n)
            return
        if isinstance(term, LiquidApp):
            op = term.fun.name
            if op == "&&" and len(term.args) == 2:
                for arg in term.args:
                    self.conclusion(arg, nonnegative, equalities, variables, n)
                return
            if op in ("==", ">=", ">", "<=", "<") and len(term.args) == 2:
                p = self.difference(term, variables, n)
                if op in ("<=", "<"):
                    p = self.scale(p, -1)
                self.certify(p, nonnegative, equalities, n, strict=op in ("<", ">"))
                if op == "==":
                    self.certify(self.scale(p, -1), nonnegative, equalities, n)
                return
        raise UnsupportedSynthesisGoal(f"Polynomial backend needs conjunctive numeric conclusions, got {term}")

    def build(self):
        for clause in self.problem.clauses:
            for branch in self.branches(clause.premise):
                # The compiler introduces value binders: v = hole(x) => P(v).
                # Eliminating these definitions before certificate generation avoids
                # needless ideal multipliers and preserves the universal obligation.
                conclusion = clause.conclusion
                allowed = {name for name, _ in clause.variables}
                while True:
                    definition = None
                    for i, atom in enumerate(branch):
                        if isinstance(atom, LiquidApp) and atom.fun.name == "==":
                            for variable, expression in (atom.args, atom.args[::-1]):
                                if (
                                    isinstance(variable, LiquidVar)
                                    and variable.name in allowed
                                    and variable.name not in liquid_free_vars(expression)
                                ):
                                    definition = i, variable.name, expression
                                    break
                        if definition is not None:
                            break
                    if definition is None:
                        break
                    i, name, expression = definition
                    branch = [substitution_in_liquid(a, expression, name) for j, a in enumerate(branch) if j != i]
                    conclusion = substitution_in_liquid(conclusion, expression, name)
                free = {name for t in [*branch, conclusion] for name in liquid_free_vars(t)}
                if any(base not in (t_int, t_float) and name in free for name, base in clause.variables):
                    raise UnsupportedSynthesisGoal(
                        "Polynomial obligations need numeric variables after eliminating definitions"
                    )
                active = [name for name, _ in clause.variables if name in free]
                n = len(active)
                variables = {
                    name: {tuple(int(j == i) for j in range(n)): z3.RealVal(1)} for i, name in enumerate(active)
                }
                nonnegative, equalities = [], []
                for atom in branch:
                    assert isinstance(atom, LiquidApp)
                    p = self.difference(atom, variables, n)
                    if atom.fun.name == "==":
                        equalities.append(p)
                    else:
                        nonnegative.append(self.scale(p, -1) if atom.fun.name in ("<", "<=") else p)
                self.conclusion(conclusion, nonnegative, equalities, variables, n)

    def solve(self) -> JointCandidate:
        self.build()
        self.solver.set(timeout=self.remaining_ms())
        result = self.solver.check()
        if result != z3.sat:
            detail = "no certificate at the configured degrees" if result == z3.unsat else self.solver.reason_unknown()
            raise SynthesisNotSuccessful(f"Polynomial synthesis: {detail}")
        model = self.solver.model()
        terms = []
        for hole, template in self.templates.values():
            body: Term | None = None
            for powers, coefficient in template.items():
                value = model.eval(coefficient, model_completion=True)
                if z3.is_int_value(value):
                    fraction = Fraction(value.as_long())
                elif z3.is_rational_value(value):
                    fraction = Fraction(value.numerator_as_long(), value.denominator_as_long())
                else:
                    raise SynthesisNotSuccessful("Polynomial synthesis cannot emit an irrational program coefficient")
                if not fraction:
                    continue
                if hole.base == t_float and any(abs(v) > 2**53 for v in (fraction.numerator, fraction.denominator)):
                    raise SynthesisNotSuccessful(
                        "Polynomial coefficient cannot be represented exactly by Float literals"
                    )
                piece = _num_literal(fraction.numerator, hole.base)
                if fraction.denominator != 1:
                    piece = _apply_op("/", hole.base, piece, _num_literal(fraction.denominator, hole.base))
                for (name, _), power in zip(hole.params, powers):
                    for _ in range(power):
                        piece = _apply_op("*", hole.base, piece, Var(name))
                body = piece if body is None else _apply_op("+", hole.base, body, piece)
            terms.append(hole.wrap(body if body is not None else _num_literal(0, hole.base)))
        return JointCandidate(tuple(terms))


def solve_polynomial(problem: SolverProblem, config: PolynomialConfig, budget: float) -> JointCandidate:
    """Generate and solve existential coefficient constraints within one budget."""
    return CertificateProblem(problem, config, time.monotonic() + budget).solve()


class PolynomialSynthesizer(ConstraintSynthesizer):
    """Polynomial templates, shared VCs and bounded algebraic proof certificates."""

    requires_whole_program = True

    def __init__(self, config: PolynomialConfig | None = None):
        self.config = config if config is not None else PolynomialConfig.from_env()

    def synthesize_joint(self, holes, validate, evaluate, fun_name, metadata, budget=60, ui=SynthesisUI()):
        started = time.monotonic()
        candidate = solve_polynomial(metadata[fun_name]["solver_problem"], self.config, budget)
        if not validate(candidate):
            raise SynthesisNotSuccessful("Polynomial synthesis: complete assignment failed validation")
        scores = evaluate(candidate) if metadata[fun_name].get("goals") else []
        ui.register(candidate, scores, time.monotonic() - started, True)
        return candidate
