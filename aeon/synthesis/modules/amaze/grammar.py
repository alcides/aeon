"""Finite typed, positive-cost derivation grammar used by AMaze's actual search.

Order: cost, stable production ID, argument-cost composition, mixed-radix child
rank. Counts are derivations, not distinct expanded ASTs or semantic classes.
A tied macro parameter is one child, even if expanded more than once.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from math import prod
from time import monotonic
from typing import Iterator

SORTS = ("Int", "Bool")
# Fixed language semantics, not learned data. No division, effects or recursion.
SIGNATURES = {
    "+": (("Int", "Int"), "Int"),
    "-": (("Int", "Int"), "Int"),
    "*": (("Int", "Int"), "Int"),
    **{op: (("Int", "Int"), "Bool") for op in ("<", "<=", ">", ">=", "==I", "!=I")},
    **{op: (("Bool", "Bool"), "Bool") for op in ("&&", "||", "-->", "==B", "!=B")},
    "!": (("Bool",), "Bool"),
    "ifI": (("Bool", "Int", "Int"), "Int"),
    "ifB": (("Bool", "Bool", "Bool"), "Bool"),
}
GRAMMAR_VERSION = "typed-cost-derivations-v1"
FEATURE_VERSION = "whole-expression-cumulative-rank-v1"


@dataclass(frozen=True)
class Expr:
    op: str
    sort: str
    children: tuple[Expr, ...] = ()
    value: int | bool | None = None

    def data(self):
        return [self.op, self.sort, self.value, [c.data() for c in self.children]]

    @staticmethod
    def read(data, depth=0):
        if depth > 24 or not isinstance(data, list) or len(data) != 4:
            raise ValueError("invalid expression template")
        op, sort, value, children = data
        if sort not in SORTS or not isinstance(op, str) or not isinstance(children, list) or len(children) > 4:
            raise ValueError("invalid expression shape")
        return Expr(op, sort, tuple(Expr.read(c, depth + 1) for c in children), value)


def size(expr: Expr) -> int:
    return 1 + sum(size(c) for c in expr.children)


def validate_expr(expr: Expr, parameters: tuple[str, ...], *, template=False) -> str:
    if expr.op in {"var", "param"}:
        if expr.op != ("param" if template else "var") or type(expr.value) is not int:
            raise ValueError("invalid variable")
        if not 0 <= expr.value < len(parameters) or expr.sort != parameters[expr.value] or expr.children:
            raise ValueError("variable type/scope mismatch")
    elif expr.op == "const":
        if expr.children or type(expr.value) is not (int if expr.sort == "Int" else bool):
            raise ValueError("invalid literal")
        if expr.sort == "Int" and expr.value not in (0, 1):
            raise ValueError("literal outside the fixed primitive grammar")
    else:
        if expr.op not in SIGNATURES or expr.value is not None:
            raise ValueError("unknown primitive or executable payload")
        args, result = SIGNATURES[expr.op]
        if expr.sort != result or tuple(validate_expr(c, parameters, template=template) for c in expr.children) != args:
            raise ValueError("primitive type mismatch")
    return expr.sort


def instantiate(template: Expr, args: tuple[Expr, ...]) -> Expr:
    if template.op == "param":
        return args[int(template.value)]
    return Expr(template.op, template.sort, tuple(instantiate(c, args) for c in template.children), template.value)


def match(template: Expr, expression: Expr, arity: int) -> tuple[Expr, ...] | None:
    bindings: dict[int, Expr] = {}

    def go(t, e):
        if t.sort != e.sort:
            return False
        if t.op == "param":
            i = int(t.value)
            if i in bindings:
                return bindings[i] == e
            bindings[i] = e
            return True
        return (
            t.op == e.op
            and t.value == e.value
            and len(t.children) == len(e.children)
            and all(go(a, b) for a, b in zip(t.children, e.children))
        )

    if go(template, expression) and set(bindings) == set(range(arity)):
        return tuple(bindings[i] for i in range(arity))
    return None


@dataclass(frozen=True)
class Production:
    id: str
    arguments: tuple[str, ...]
    result: str
    template: Expr
    cost: int = 1

    def __post_init__(self):
        if type(self.cost) is not int or self.cost <= 0:
            raise ValueError("production costs must be positive; zero-cost cycles are unsupported")
        if self.result not in SORTS or any(a not in SORTS for a in self.arguments):
            raise ValueError("invalid production sorts")
        # Variable leaves are instance-specific. All other templates are closed.
        if self.template.op != "var":
            if validate_expr(self.template, self.arguments, template=True) != self.result:
                raise ValueError("production result mismatch")
            used = set()

            def visit(e):
                if e.op == "param":
                    used.add(e.value)
                for c in e.children:
                    visit(c)

            visit(self.template)
            if used != set(range(len(self.arguments))):
                raise ValueError("every macro parameter must occur")
        elif self.arguments or self.result != self.template.sort or type(self.template.value) is not int:
            raise ValueError("invalid variable production")


def base_productions(inputs: tuple[str, ...]) -> tuple[Production, ...]:
    result = [Production(f"var:{i:04}", (), sort, Expr("var", sort, value=i)) for i, sort in enumerate(inputs)]
    for sort, values in (("Int", (0, 1)), ("Bool", (False, True))):
        result += [Production(f"const:{sort}:{v}", (), sort, Expr("const", sort, value=v)) for v in values]
    for op, (args, out) in SIGNATURES.items():
        result.append(
            Production(
                f"op:{op}", args, out, Expr(op, out, tuple(Expr("param", s, value=i) for i, s in enumerate(args)))
            )
        )
    return tuple(result)


@lru_cache(maxsize=4096)
def compositions(total: int, arity: int) -> tuple[tuple[int, ...], ...]:
    if arity == 0:
        return ((),) if total == 0 else ()
    if arity == 1:
        return ((total,),) if total >= 1 else ()
    return tuple(
        (first, *rest) for first in range(1, total - arity + 2) for rest in compositions(total - first, arity - 1)
    )


class Grammar:
    def __init__(self, productions: tuple[Production, ...]):
        self.productions = tuple(sorted(productions, key=lambda p: p.id))
        if len({p.id for p in productions}) != len(productions):
            raise ValueError("production IDs must be unique")
        self._counts: dict[tuple[str, int], int] = {}
        self._rewrites: dict[Expr, int | None] = {}

    def count(self, sort: str, cost: int) -> int:
        key = (sort, cost)
        if key not in self._counts:
            self._counts[key] = (
                0
                if cost <= 0
                else sum(
                    prod(self.count(s, n) for s, n in zip(p.arguments, allocation))
                    for p in self.productions
                    if p.result == sort
                    for allocation in compositions(cost - p.cost, len(p.arguments))
                )
            )
        return self._counts[key]

    def rank_bound(self, sort: str, cost: int) -> int:
        return sum(self.count(sort, n) for n in range(1, cost + 1))

    def unrank(self, sort: str, cost: int, index: int) -> tuple[Expr, tuple[str, ...]]:
        if not 0 <= index < self.count(sort, cost):
            raise IndexError("derivation rank outside grammar")
        for p in self.productions:
            if p.result != sort:
                continue
            for allocation in compositions(cost - p.cost, len(p.arguments)):
                counts = [self.count(s, n) for s, n in zip(p.arguments, allocation)]
                block = prod(counts)
                if index >= block:
                    index -= block
                    continue
                args, ids = [], [p.id]
                for i, (s, n) in enumerate(zip(p.arguments, allocation)):
                    stride = prod(counts[i + 1 :])
                    child, used = self.unrank(s, n, index // stride)
                    index %= stride
                    args.append(child)
                    ids.extend(used)
                return instantiate(p.template, tuple(args)), tuple(ids)
        raise AssertionError("DP and unranking disagree")

    def rewrite_cost(self, expression: Expr) -> int | None:
        if expression not in self._rewrites:
            best = None
            for p in self.productions:
                if p.result != expression.sort:
                    continue
                args = match(p.template, expression, len(p.arguments))
                if args is None or any(arg == expression for arg in args):
                    continue
                costs = [self.rewrite_cost(arg) for arg in args]
                if any(c is None for c in costs):
                    continue
                cost = p.cost + sum(c for c in costs if c is not None)
                best = cost if best is None else min(best, cost)
            self._rewrites[expression] = best
        return self._rewrites[expression]

    def estimate(self, expression: Expr) -> int | None:
        cost = self.rewrite_cost(expression)
        return None if cost is None else self.rank_bound(expression.sort, cost)

    def enumerate(
        self, sort: str, max_cost: int, max_candidates: int, deadline: float
    ) -> Iterator[tuple[Expr, int, tuple[str, ...]]]:
        generated = 0
        for cost in range(1, max_cost + 1):
            for index in range(min(self.count(sort, cost), max_candidates - generated)):
                if monotonic() >= deadline:
                    return
                expression, ids = self.unrank(sort, cost, index)
                generated += 1
                yield expression, cost, ids
            if generated >= max_candidates:
                return


def evaluate(expr: Expr, inputs: tuple[int | bool, ...]):
    if expr.op == "var":
        return inputs[int(expr.value)]
    if expr.op == "const":
        return expr.value
    if expr.op in ("ifI", "ifB"):
        return evaluate(expr.children[1 if evaluate(expr.children[0], inputs) else 2], inputs)
    values = [evaluate(c, inputs) for c in expr.children]
    a = values[0]
    b = values[1] if len(values) > 1 else None
    operations = {
        "+": lambda: a + b,
        "-": lambda: a - b,
        "*": lambda: a * b,
        "<": lambda: a < b,
        "<=": lambda: a <= b,
        ">": lambda: a > b,
        ">=": lambda: a >= b,
        "==I": lambda: a == b,
        "==B": lambda: a == b,
        "!=I": lambda: a != b,
        "!=B": lambda: a != b,
        "&&": lambda: a and b,
        "||": lambda: a or b,
        "!": lambda: not a,
        "-->": lambda: not a or b,
    }
    return operations[expr.op]()


def probes(sorts: tuple[str, ...]):
    return tuple(product(*[(False, True) if s == "Bool" else (-2, -1, 0, 1, 2) for s in sorts]))
