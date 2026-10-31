"""Acyclic tree languages and context-indexed lifted interpretation.

Unlike a bank of representative terms, every state retains *all* transitions
producing its observation. Specializing an already specialized state intersects
its language with a new behavior. This is the footprint-extension invariant of
Li et al., POPL 2024, Sections 3 and Appendix A (arXiv:2311.03705).
"""

from __future__ import annotations

import itertools
import operator
from dataclasses import dataclass
from time import monotonic
from typing import Any, Callable, Iterator

from aeon.core.terms import If, Literal, Term, TypeApplication, Var
from aeon.core.types import Type, t_bool, t_int
from aeon.synthesis.api import SynthesisNotSuccessful, UnsupportedSynthesisGoal
from aeon.synthesis.modules.bottom_up import application
from aeon.utils.name import Name


OPERATORS: dict[str, Callable[..., Any]] = {
    "+": operator.add,
    "-": operator.sub,
    "*": operator.mul,
    "==": operator.eq,
    "!=": operator.ne,
    "<": operator.lt,
    "<=": operator.le,
    ">": operator.gt,
    ">=": operator.ge,
    "&&": lambda x, y: x and y,
    "||": lambda x, y: x or y,
    "!": operator.not_,
    "-->": lambda x, y: (not x) or y,
}


def scalar_key(value: Any) -> tuple[type, Any]:
    if type(value) not in (int, bool):
        raise UnsupportedSynthesisGoal("arborist observations must be Int or Bool")
    if type(value) is int and value.bit_length() > 4096:
        raise SynthesisNotSuccessful("arborist 4096-bit integer limit exhausted")
    return (type(value), value)


@dataclass
class SearchStats:
    transitions: int = 0
    merges: int = 0
    contexts: int = 0
    cache_hits: int = 0
    interpreter_steps: int = 0
    validated: int = 0


@dataclass(frozen=True)
class Label:
    kind: str
    term: Term
    result: Type
    arguments: tuple[Type, ...] = ()
    operator: str = ""

    def build(self, children: tuple[Term, ...]) -> Term:
        if self.kind == "if":
            return If(children[0], children[1], children[2])
        return application(self.term, children)


@dataclass(frozen=True)
class Edge:
    label: int
    children: tuple[int, ...] = ()


@dataclass(frozen=True)
class State:
    # Keep grammar nonterminals distinct, even if observations happen to agree.
    symbol: tuple[Type, int]
    edges: tuple[Edge, ...]


class Forest:
    def __init__(self, labels: list[Label], deadline: float, *, compress: bool = True, max_states: int = 100_000):
        self.labels = labels
        self.deadline = deadline
        self.compress = compress
        self.max_states = max_states
        self.stats = SearchStats()
        self.states: list[State] = []
        self._interned: dict[State, int] = {}
        self._grammar: dict[tuple[Type, int], int] = {}
        self._cache: dict[tuple, list[tuple[Any, int]]] = {}
        self._contexts: set[tuple] = set()
        self._counts: dict[int, int] = {}
        self.variables = tuple(
            dict.fromkeys(
                label.term.name for label in labels if isinstance(label.term, Var) and label.kind == "variable"
            )
        )

    def check_budget(self) -> None:
        if monotonic() >= self.deadline:
            raise SynthesisNotSuccessful("arborist search budget exhausted")

    def intern(self, symbol: tuple[Type, int], edges: list[Edge]) -> int:
        self.check_budget()
        state = State(symbol, tuple(sorted(set(edges), key=lambda edge: (edge.label, edge.children))))
        previous = self._interned.get(state)
        if previous is not None:
            return previous
        if len(self.states) >= self.max_states:
            raise SynthesisNotSuccessful("arborist packed-state limit exhausted")
        result = len(self.states)
        self.states.append(state)
        self._interned[state] = result
        return result

    def grammar(self, ty: Type, depth: int) -> int:
        """Typed expressions with at most ``depth`` nested operations."""
        symbol = (ty, depth)
        if symbol not in self._grammar:
            edges = []
            for index, label in enumerate(self.labels):
                if label.result != ty or (label.arguments and depth == 0):
                    continue
                children = tuple(self.grammar(arg, depth - 1) for arg in label.arguments)
                if all(self.states[child].edges for child in children):
                    edges.append(Edge(index, children))
            self._grammar[symbol] = self.intern(symbol, edges)
        return self._grammar[symbol]

    def union(self, states: list[int]) -> int:
        assert states
        symbol = self.states[states[0]].symbol
        assert all(self.states[state].symbol == symbol for state in states)
        return self.intern(symbol, [edge for state in states for edge in self.states[state].edges])

    def specialize(self, state_id: int, bindings: dict[Name, Any]) -> list[tuple[Any, int]]:
        """Partition exactly this language by its result in this context.

        Children are specialized before parents, and parent transitions combine
        child *classes*, not individual programs. All alternatives are retained,
        so later contexts can split a class without recovering discarded terms.
        ``compress=False`` is the small-grammar exhaustive ablation.
        """
        self.check_budget()
        context = tuple(scalar_key(bindings[name]) for name in self.variables)
        cache_key = (state_id, context)
        if cache_key in self._cache:
            self.stats.cache_hits += 1
            return self._cache[cache_key]
        self._contexts.add(context)
        self.stats.contexts = len(self._contexts)
        state = self.states[state_id]
        groups: dict[Any, tuple[Any, list[Edge]]] = {}
        for edge in state.edges:
            self.check_budget()
            label = self.labels[edge.label]
            pools = [self.specialize(child, bindings) for child in edge.children]
            for choices in itertools.product(*pools):
                self.check_budget()
                self.stats.transitions += 1
                values = tuple(value for value, _ in choices)
                if label.kind == "variable":
                    assert isinstance(label.term, Var)
                    value = bindings[label.term.name]
                elif label.kind == "literal":
                    assert isinstance(label.term, Literal)
                    value = label.term.value
                elif label.kind == "if":
                    value = values[1] if values[0] else values[2]
                else:
                    value = OPERATORS[label.operator](*values)
                key: Any = scalar_key(value)
                if not self.compress:
                    key = (key, len(groups))
                restricted = Edge(edge.label, tuple(child for _, child in choices))
                if key in groups:
                    self.stats.merges += 1
                    groups[key][1].append(restricted)
                else:
                    groups[key] = (value, [restricted])
        result = [(value, self.intern(state.symbol, edges)) for value, edges in groups.values()]
        self._cache[cache_key] = result
        return result

    def terms(self, state_id: int) -> Iterator[Term]:
        """Extract every surviving alternative, lazily, for refinement checks.

        Example-equivalent terms can differ on unobserved inputs, so rejection
        of one representative must not discard the rest of its language.
        """
        for edge in self.states[state_id].edges:
            self.check_budget()
            for children in self._products(edge.children):
                yield self.labels[edge.label].build(children)

    def _products(self, children: tuple[int, ...]) -> Iterator[tuple[Term, ...]]:
        if not children:
            yield ()
        else:
            for head in self.terms(children[0]):
                for tail in self._products(children[1:]):
                    yield (head, *tail)

    def count(self, state_id: int) -> int:
        """Number of syntax trees represented, without expanding them."""
        if state_id not in self._counts:
            total = 0
            for edge in self.states[state_id].edges:
                product = 1
                for child in edge.children:
                    product *= self.count(child)
                total += product
            self._counts[state_id] = total
        return self._counts[state_id]


def scalar_labels(
    variables: list[tuple[Name, Type]],
    available: set[Name],
    *,
    constants: tuple[int, ...] = (0, 1, 2),
    operators: tuple[str, ...] = ("+", "-", "*", "==", "<", "<=", "&&", "||", "!"),
    conditionals: bool = True,
) -> list[Label]:
    labels = [Label("variable", Var(name), ty) for name, ty in variables]
    labels.extend(Label("literal", Literal(value, t_int), t_int) for value in constants)
    labels.extend(Label("literal", Literal(value, t_bool), t_bool) for value in (False, True))
    for op in operators:
        if op not in OPERATORS:
            raise ValueError(f"Unsupported grammar operator: {op}")
        name = Name(op, 0)
        if name not in available:
            continue
        boolean = op in ("&&", "||", "!", "-->")
        arg = t_bool if boolean else t_int
        result = t_int if op in ("+", "-", "*") else t_bool
        head: Term = Var(name) if boolean else TypeApplication(Var(name), t_int)
        labels.append(Label("operation", head, result, (arg,) if op == "!" else (arg, arg), op))
    if conditionals:
        for ty in (t_int, t_bool):
            labels.append(Label("if", Var(Name("if", 0)), ty, (t_bool, ty, ty)))
    return labels
