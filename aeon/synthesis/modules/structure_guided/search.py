"""Bounded structure/element separation for recursive list-producing programs.

List constructors and append normalize to words of element holes and calls on
immediate input children. Size recurrences prune these words before diamond
alignment extracts local integer PBE tasks. No reference implementation of a
target transformation is part of the search grammar.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from itertools import product
import os
import time

from aeon.synthesis.api import SynthesisNotSuccessful, UnsupportedSynthesisGoal


@dataclass(frozen=True)
class Node:
    values: tuple[int, ...]
    children: tuple[Node | None, ...]


@dataclass(frozen=True)
class Example:
    input: Node | None
    output: tuple[int, ...]


@dataclass(frozen=True)
class Config:
    max_calls: int = 2
    max_added: int = 3
    max_base: int = 1
    max_element_size: int = 7
    max_values: int = 5000
    max_nodes: int = 128
    max_depth: int = 16
    max_skeletons: int = 10000

    def __post_init__(self):
        if min(self.max_calls, self.max_added, self.max_base) < 0:
            raise UnsupportedSynthesisGoal("structure_guided: grammar bounds must be nonnegative")
        if min(self.max_element_size, self.max_values, self.max_nodes, self.max_depth, self.max_skeletons) < 1:
            raise UnsupportedSynthesisGoal("structure_guided: search limits must be positive")

    @classmethod
    def from_env(cls):
        try:
            return cls(
                **{
                    field: int(os.environ["AEON_STRUCTURE_" + field.upper()])
                    for field in cls.__dataclass_fields__
                    if "AEON_STRUCTURE_" + field.upper() in os.environ
                }
            )
        except ValueError as exc:
            raise UnsupportedSynthesisGoal("structure_guided: search limits must be integers") from exc


@dataclass
class Stats:
    recurrences: int = 0
    prefixes: int = 0
    pruned: int = 0
    aligned: int = 0
    local_tasks: int = 0
    local_values: int = 0
    candidates: int = 0
    validation_rejections: int = 0
    runtime_rejections: int = 0


@dataclass(frozen=True)
class Recurrence:
    calls: tuple[int, ...]
    added: int
    base: int


@dataclass(frozen=True)
class Expr:
    op: str
    value: int = 0
    args: tuple[Expr, ...] = ()

    def evaluate(self, inputs: tuple[int, ...]) -> int:
        if self.op == "var":
            return inputs[self.value]
        if self.op == "const":
            return self.value
        a, b = (arg.evaluate(inputs) for arg in self.args)
        return {"+": lambda: a + b, "-": lambda: a - b, "*": lambda: a * b}[self.op]()


@dataclass(frozen=True)
class Diamond:
    slot: tuple[int, int]  # branch (base/step), position in its normalized word
    inputs: tuple[int, ...]


@dataclass(frozen=True)
class Solution:
    # -1 is one constructor with an element hole; i >= 0 is f(child_i).
    word: tuple[int, ...]
    base: int
    elements: dict[tuple[int, int], Expr]


class Search:
    def __init__(self, examples: tuple[Example, ...], arity: int, config: Config, budget: float):
        self.examples = examples
        self.arity = arity
        self.config = config
        self.deadline = time.monotonic() + budget
        self.stats = Stats()
        self.local_cache: dict[tuple, Expr | None] = {}
        if not examples or not 1 <= arity <= 2:
            raise UnsupportedSynthesisGoal("structure_guided: needs examples and one or two recursive input fields")
        for example in examples:
            remaining = config.max_nodes

            def visit(node, depth):
                nonlocal remaining
                self.tick()
                remaining -= 1
                if depth > config.max_depth or remaining < 0:
                    raise UnsupportedSynthesisGoal("structure_guided: input exceeds structural bounds")
                if node is not None:
                    if (
                        not isinstance(node, Node)
                        or len(node.children) != arity
                        or any(type(v) is not int for v in node.values)
                    ):
                        raise UnsupportedSynthesisGoal("structure_guided: malformed input node")
                    for child in node.children:
                        visit(child, depth + 1)

            visit(example.input, 0)
            if len(example.output) > config.max_nodes or any(type(v) is not int for v in example.output):
                raise UnsupportedSynthesisGoal("structure_guided: output must be a bounded integer list")

    def tick(self):
        if time.monotonic() >= self.deadline:
            raise SynthesisNotSuccessful("structure_guided: time budget exhausted")

    def recurrences(self) -> tuple[Recurrence, ...]:
        """Retain every bounded recurrence consistent with ALL complete examples."""
        result = []
        for calls in product(range(self.config.max_calls + 1), repeat=self.arity):
            if sum(calls) > self.config.max_calls:
                continue
            for added, base in product(range(self.config.max_added + 1), range(self.config.max_base + 1)):
                self.tick()

                def size(node):
                    self.tick()
                    if node is None:
                        return base
                    return added + sum(a * size(child) for a, child in zip(calls, node.children))

                if all(size(e.input) == len(e.output) for e in self.examples):
                    result.append(Recurrence(calls, added, base))
        self.stats.recurrences = len(result)
        return tuple(result)

    def words(self, recurrences: tuple[Recurrence, ...]):
        """Expand prefixes top-down; element expressions remain uninstantiated."""
        queue: deque[tuple[int, ...]] = deque([()])
        while queue:
            self.tick()
            word = queue.popleft()
            self.stats.prefixes += 1
            if self.stats.prefixes > self.config.max_skeletons:
                raise SynthesisNotSuccessful("structure_guided: skeleton limit exhausted")
            calls = tuple(word.count(i) for i in range(self.arity))
            added = word.count(-1)
            feasible = [r for r in recurrences if added <= r.added and all(a <= b for a, b in zip(calls, r.calls))]
            if not feasible:
                self.stats.pruned += 1
                continue
            complete = {r.base for r in feasible if r.calls == calls and r.added == added}
            if not complete:
                self.stats.pruned += 1  # closing this partial constructor word is impossible
            for base in sorted(complete):
                yield word, base
            if any(added < r.added or calls != r.calls for r in feasible):
                queue.extend(word + (token,) for token in range(-1, self.arity))

    def trace(self, word: tuple[int, ...], base: int, node: Node | None) -> tuple[Diamond, ...]:
        self.tick()
        if node is None:
            return tuple(Diamond((0, i), ()) for i in range(base))
        out: list[Diamond] = []
        for i, token in enumerate(word):
            if token == -1:
                out.append(Diamond((1, i), node.values))
            else:
                out.extend(self.trace(word, base, node.children[token]))
            if len(out) > self.config.max_nodes:
                raise SynthesisNotSuccessful("structure_guided: symbolic output exceeded its node limit")
        return tuple(out)

    def align(self, word: tuple[int, ...], base: int) -> dict[tuple[int, int], dict[tuple[int, ...], int]] | None:
        """Align fully unrolled constructor output with examples to extract local tasks."""
        tasks: dict[tuple[int, int], dict[tuple[int, ...], int]] = {
            **{(0, i): {} for i in range(base)},
            **{(1, i): {} for i, token in enumerate(word) if token == -1},
        }
        for example in self.examples:
            trace = self.trace(word, base, example.input)
            if len(trace) != len(example.output):
                return None
            for diamond, value in zip(trace, example.output):
                task = tasks[diamond.slot]
                if diamond.inputs in task and task[diamond.inputs] != value:
                    return None
                task[diamond.inputs] = value
        self.stats.aligned += 1
        return tasks

    def element(self, task: dict[tuple[int, ...], int]) -> Expr | None:
        """Size-ordered integer PBE with observational equivalence per local task."""
        self.tick()
        key = tuple(sorted(task.items()))
        if key in self.local_cache:
            return self.local_cache[key]
        self.stats.local_tasks += 1
        if not task:
            return Expr("const", 0)  # unobserved hole; whole-program validation still applies
        inputs, expected = zip(*key)
        arity = len(inputs[0])
        if any(len(row) != arity for row in inputs):
            raise UnsupportedSynthesisGoal("structure_guided: inconsistent local element arity")
        levels: dict[int, list[tuple[Expr, tuple[int, ...]]]] = {}
        observed = set()

        def insert(size, expression, values):
            if any(v.bit_length() > 256 for v in values) or values in observed:
                return False
            observed.add(values)
            if len(observed) > self.config.max_values:
                raise SynthesisNotSuccessful("structure_guided: local element value limit exhausted")
            self.stats.local_values += 1
            levels.setdefault(size, []).append((expression, values))
            return True

        constants = list(dict.fromkeys([0, 1, -1, 2, *expected]))[:32]
        atoms = [Expr("var", i) for i in range(arity)] + [Expr("const", c) for c in constants]
        for expression in atoms:
            values = tuple(expression.evaluate(row) for row in inputs)
            insert(1, expression, values)
        for size in range(1, self.config.max_element_size + 1):
            self.tick()
            if size > 1:
                for left_size in range(1, size - 1):
                    right_size = size - 1 - left_size
                    for left, lv in levels.get(left_size, []):
                        for right, rv in levels.get(right_size, []):
                            self.tick()
                            for op in ("+", "-", "*"):
                                values = tuple(
                                    a + b if op == "+" else a - b if op == "-" else a * b for a, b in zip(lv, rv)
                                )
                                insert(size, Expr(op, args=(left, right)), values)
                                if values == expected:
                                    expression = Expr(op, args=(left, right))
                                    self.local_cache[key] = expression
                                    return expression
                                if len(observed) >= self.config.max_values:
                                    raise SynthesisNotSuccessful(
                                        "structure_guided: local element value limit exhausted"
                                    )
            for expression, values in levels.get(size, []):
                if values == expected:
                    self.local_cache[key] = expression
                    return expression
        self.local_cache[key] = None
        return None

    def solutions(self):
        recurrences = self.recurrences()
        if not recurrences:
            raise SynthesisNotSuccessful("structure_guided: no size recurrence within the configured grammar")
        for word, base in self.words(recurrences):
            tasks = self.align(word, base)
            if tasks is None:
                self.stats.pruned += 1
                continue
            elements = {}
            for slot, task in tasks.items():
                expression = self.element(task)
                if expression is None:
                    break
                elements[slot] = expression
            else:
                self.stats.candidates += 1
                yield Solution(word, base, elements)
