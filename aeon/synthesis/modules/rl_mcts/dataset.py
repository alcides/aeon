"""Section 4: generate solvable LIA synthesis tasks from valid SMT formulas.

The least general generalizer preserves repeated disagreement pairs. Its fresh
variables become synthesis parameters; matching recovers each call's arguments.
The witness is for validation/testing only and is never supplied to search.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations

import z3
from z3.z3util import get_vars

from aeon.synthesis.modules.rl_mcts.features import Syntax
from aeon.synthesis.modules.rl_mcts.search import Guidance, SearchConfig, SearchResult, search


def _valid(formula: z3.BoolRef, timeout_ms: int = 2000) -> bool:
    solver = z3.Solver()
    solver.set(timeout=timeout_ms)
    solver.add(z3.Not(formula))
    return solver.check() == z3.unsat


def _check_fragment(expr: z3.ExprRef) -> None:
    allowed = {
        z3.Z3_OP_UNINTERPRETED,
        z3.Z3_OP_ANUM,
        z3.Z3_OP_TRUE,
        z3.Z3_OP_FALSE,
        z3.Z3_OP_ADD,
        z3.Z3_OP_SUB,
        z3.Z3_OP_UMINUS,
        z3.Z3_OP_MUL,
        z3.Z3_OP_IDIV,
        z3.Z3_OP_MOD,
        z3.Z3_OP_LE,
        z3.Z3_OP_GE,
        z3.Z3_OP_LT,
        z3.Z3_OP_GT,
        z3.Z3_OP_EQ,
        z3.Z3_OP_DISTINCT,
        z3.Z3_OP_ITE,
        z3.Z3_OP_AND,
        z3.Z3_OP_OR,
        z3.Z3_OP_NOT,
        z3.Z3_OP_IMPLIES,
    }
    if not z3.is_app(expr) or expr.sort().kind() not in {z3.Z3_INT_SORT, z3.Z3_BOOL_SORT}:
        raise ValueError("data generation supports quantifier-free Int/Bool LIA only")
    if expr.decl().kind() not in allowed or (expr.decl().kind() == z3.Z3_OP_UNINTERPRETED and expr.num_args()):
        raise ValueError("unsupported operator in LIA training source")
    if expr.decl().kind() == z3.Z3_OP_MUL and sum(not z3.is_int_value(z3.simplify(c)) for c in expr.children()) > 1:
        raise ValueError("nonlinear multiplication is outside LIA")
    if expr.decl().kind() in {z3.Z3_OP_IDIV, z3.Z3_OP_MOD} and not z3.is_int_value(z3.simplify(expr.arg(1))):
        raise ValueError("LIA division/modulo needs a constant divisor")
    for child in expr.children():
        _check_fragment(child)


@dataclass
class Generalization:
    term: z3.ExprRef
    params: tuple[z3.ExprRef, ...]
    arguments: tuple[tuple[z3.ExprRef, ...], ...]


def anti_unify(terms: tuple[z3.ExprRef, ...]) -> Generalization:
    if len(terms) < 2 or any(t.sort() != terms[0].sort() for t in terms):
        raise ValueError("anti-unification needs at least two terms of the same sort")
    for term in terms:
        _check_fragment(term)
    params: list[z3.ExprRef] = []
    arguments: list[tuple[z3.ExprRef, ...]] = []
    memo: dict[tuple[str, ...], z3.ExprRef] = {}

    def generalize(group: tuple[z3.ExprRef, ...]) -> z3.ExprRef:
        # Source variables must also become parameters, even when identical in
        # every term: the new synthesis function cannot capture those globals.
        common = all(t.eq(group[0]) for t in group)
        variable = z3.is_const(group[0]) and group[0].decl().kind() == z3.Z3_OP_UNINTERPRETED
        if common and not variable and not get_vars(group[0]):
            return group[0]
        same_head = all(t.decl() == group[0].decl() and t.num_args() == group[0].num_args() for t in group)
        if same_head and group[0].num_args():
            return group[0].decl()(*[generalize(tuple(t.arg(i) for t in group)) for i in range(group[0].num_args())])
        key = tuple(f"{t.sort()}:{t.sexpr()}" for t in group)
        if key not in memo:
            memo[key] = z3.FreshConst(group[0].sort(), prefix="arg")
            params.append(memo[key])
            arguments.append(group)
        return memo[key]

    pattern = generalize(terms)
    calls = tuple(tuple(group[i] for group in arguments) for i in range(len(terms)))
    return Generalization(pattern, tuple(params), calls)


def _contains(container: z3.ExprRef, target: z3.ExprRef) -> bool:
    return container.eq(target) or any(_contains(c, target) for c in container.children())


@dataclass
class GeneratedProblem:
    formula: z3.BoolRef
    function: z3.FuncDeclRef
    params: tuple[z3.ExprRef, ...]
    witness: z3.ExprRef
    constants: tuple[int, ...] = (-1, 0, 1)

    def instantiate(self, candidate: z3.ExprRef) -> z3.BoolRef:
        if candidate.sort().kind() != z3.Z3_INT_SORT:
            raise ValueError("candidate must return Int")
        if any(not any(v.eq(p) for p in self.params) for v in get_vars(candidate)):
            raise ValueError("candidate has variables outside the synthesis parameters")

        def replace(expr: z3.ExprRef) -> z3.ExprRef:
            children = [replace(c) for c in expr.children()]
            if expr.decl() == self.function:
                return z3.substitute(candidate, *zip(self.params, children)) if self.params else candidate
            return expr.decl()(*children) if children else expr

        return replace(self.formula)

    def verify(self, candidate: z3.ExprRef) -> bool:
        return _valid(self.instantiate(candidate))

    def to_sygus(self) -> str:
        def quoted(expr: z3.ExprRef) -> str:
            return expr.sexpr()

        integer_params = " ".join(quoted(p) for p in self.params if p.sort().kind() == z3.Z3_INT_SORT)
        boolean_params = " ".join(quoted(p) for p in self.params if p.sort().kind() == z3.Z3_BOOL_SORT)
        params = " ".join(f"({quoted(p)} {p.sort()})" for p in self.params)
        variables = "\n".join(f"(declare-var {quoted(v)} {v.sort()})" for v in get_vars(self.formula))
        literals = " ".join(z3.IntVal(c).sexpr() for c in self.constants)
        arithmetic = " ".join(f"(* {z3.IntVal(c).sexpr()} I)" for c in self.constants)
        division = " ".join(
            f"(div I {z3.IntVal(c).sexpr()}) (mod I {z3.IntVal(c).sexpr()})" for c in self.constants if c
        )
        grammar = (
            f"((I Int ({literals} {integer_params} (+ I I) (- I I) (ite B I I) {arithmetic} {division})) "
            f"(B Bool (true false {boolean_params} (<= I I) (= I I) (and B B) (or B B) (not B))))"
        )
        return (
            f"(set-logic LIA)\n(synth-fun {self.function.name()} ({params}) Int ((I Int) (B Bool)) {grammar})\n"
            f"{variables}\n(constraint {self.formula.sexpr()})\n(check-synth)\n"
        )


def generate_problem(formula: z3.BoolRef, selected: tuple[z3.ExprRef, ...]) -> GeneratedProblem:
    _check_fragment(formula)
    if not _valid(formula):
        raise ValueError("training source must be valid for every assignment (unknown is rejected)")
    if any(t.sort().kind() != z3.Z3_INT_SORT or not _contains(formula, t) for t in selected):
        raise ValueError("selected terms must be Int subterms of the source")
    if any(_contains(a, b) or _contains(b, a) for a, b in combinations(selected, 2)):
        raise ValueError("selected terms must be distinct and non-overlapping")
    generalization = anti_unify(selected)
    # Generalizing different coefficients/divisors can leave the LIA fragment.
    # Such a witness would not be expressible by our linear grammar.
    _check_fragment(generalization.term)
    if z3.is_const(generalization.term):
        raise ValueError("trivial generalization: choose subterms with more common structure")
    marker = z3.FreshInt("synth")
    function = z3.Function(str(marker.decl().name()), *[p.sort() for p in generalization.params], z3.IntSort())
    substitutions = [(term, function(*args)) for term, args in zip(selected, generalization.arguments)]
    transformed = z3.substitute(formula, *substitutions)
    constants = {-1, 0, 1}

    def collect_constants(expr: z3.ExprRef) -> None:
        if z3.is_int_value(expr):
            constants.add(expr.as_long())
        for child in expr.children():
            collect_constants(child)

    collect_constants(formula)
    problem = GeneratedProblem(
        transformed, function, generalization.params, generalization.term, tuple(sorted(constants))
    )
    if not problem.verify(problem.witness):
        raise ValueError("generated witness failed validation")
    return problem


def generate_problems(formula: z3.BoolRef, limit: int = 8) -> list[GeneratedProblem]:
    """Prefer largest same-head Int generalizers, rejecting trivial/overlap pairs."""
    _check_fragment(formula)
    if limit < 1:
        raise ValueError("problem limit must be positive")
    if not _valid(formula):
        raise ValueError("training source must be universally valid")
    terms: dict[str, z3.ExprRef] = {}

    def collect(expr: z3.ExprRef) -> None:
        if expr.sort().kind() == z3.Z3_INT_SORT and expr.num_args():
            terms.setdefault(expr.sexpr(), expr)
        for child in expr.children():
            collect(child)

    collect(formula)
    pairs = [(a, b) for a, b in combinations(terms.values(), 2) if a.decl() == b.decl()]
    pairs.sort(key=lambda pair: sum(len(t.sexpr()) for t in pair), reverse=True)
    result = []
    for pair in pairs:
        if any(_contains(a, b) or _contains(b, a) for a, b in combinations(pair, 2)):
            continue
        try:
            result.append(generate_problem(formula, pair))
        except ValueError:
            continue
        if len(result) >= limit:
            break
    return result


def _z3_syntax(expr: z3.ExprRef, names: dict[str, str]) -> Syntax:
    label = names.get(str(expr.decl().name()), str(expr.decl().name()))
    return Syntax(f"{label}:{expr.sort()}", tuple(_z3_syntax(c, names) for c in expr.children()))


def solve_generated(
    problem: GeneratedProblem,
    guidance: Guidance | None = None,
    *,
    config: SearchConfig = SearchConfig(),
    budget: float = 60,
    seed: int = 0,
    max_expansions: int = 20,
) -> tuple[Syntax, SearchResult[Syntax]]:
    """Search generated tasks with the same MCTS engine; witness is not read."""
    names = {str(problem.function.name()): "synth"}
    names.update({str(p.decl().name()): f"param:{i}" for i, p in enumerate(problem.params)})
    spec = _z3_syntax(problem.formula, names)
    params = {f"param:{i}:{p.sort()}": p for i, p in enumerate(problem.params)}

    def replacements(sort: str) -> list[Syntax]:
        terminal = [Syntax(key) for key, p in params.items() if str(p.sort()) == sort]
        i, b = Syntax("hole:Int"), Syntax("hole:Bool")
        if sort == "Int":
            constants = [Syntax(str(c)) for c in problem.constants]
            arithmetic = [Syntax("*", (c, i)) for c in constants]
            division = [Syntax(op, (i, Syntax(str(c)))) for c in problem.constants if c for op in ("div", "mod")]
            return (
                terminal
                + constants
                + [Syntax("+", (i, i)), Syntax("-", (i, i)), Syntax("ite", (b, i, i))]
                + arithmetic
                + division
            )
        return terminal + [
            Syntax("true"),
            Syntax("false"),
            Syntax("<=", (i, i)),
            Syntax("=", (i, i)),
            Syntax("and", (b, b)),
            Syntax("or", (b, b)),
            Syntax("not", (b,)),
        ]

    def expand(tree: Syntax) -> list[Syntax]:
        def leftmost(node: Syntax) -> list[Syntax]:
            if node.label.startswith("hole:"):
                return replacements(node.label.removeprefix("hole:"))
            for index, child in enumerate(node.children):
                if child.holes():
                    return [
                        Syntax(node.label, node.children[:index] + (r,) + node.children[index + 1 :])
                        for r in leftmost(child)
                    ]
            return []

        def size(node: Syntax) -> int:
            return 1 + sum(size(c) for c in node.children)

        return [t for t in leftmost(tree) if size(t) <= max_expansions]

    def expression(tree: Syntax) -> z3.ExprRef:
        if tree.label in params:
            return params[tree.label]
        if tree.label in {str(c) for c in problem.constants}:
            return z3.IntVal(int(tree.label))
        if tree.label in {"true", "false"}:
            return z3.BoolVal(tree.label == "true")
        args = [expression(c) for c in tree.children]
        operations = {
            "+": lambda: args[0] + args[1],
            "-": lambda: args[0] - args[1],
            "*": lambda: args[0] * args[1],
            "div": lambda: args[0] / args[1],
            "mod": lambda: args[0] % args[1],
            "ite": lambda: z3.If(*args),
            "<=": lambda: args[0] <= args[1],
            "=": lambda: args[0] == args[1],
            "and": lambda: z3.And(*args),
            "or": lambda: z3.Or(*args),
            "not": lambda: z3.Not(args[0]),
        }
        return operations[tree.label]()

    result = search(
        Syntax("hole:Int"),
        spec,
        lambda s: s,
        lambda s: s.holes(),
        expand,
        lambda s: problem.verify(expression(s)),
        guidance=guidance,
        config=config,
        budget=budget,
        seed=seed,
    )
    return spec, result
