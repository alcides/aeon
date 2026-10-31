"""Finite additive choice-tree IR, reference traces and deterministic costs."""

from dataclasses import dataclass
from time import monotonic
import os

from aeon.synthesis.api import SynthesisNotSuccessful, UnsupportedSynthesisGoal
from aeon.synthesis.modules.dp_gp.expressions import Expr


@dataclass(frozen=True)
class Config:
    seed: int = 0
    proposals: int = 600
    epochs: int = 8
    max_nodes: int = 100000
    max_fuel: int = 8
    max_instances: int = 128

    @classmethod
    def from_env(cls, seed=0):
        values = {"seed": seed}
        for name in ("proposals", "epochs", "max_nodes", "max_fuel", "max_instances"):
            values[name] = int(os.environ.get("AEON_DP_GP_" + name.upper(), getattr(cls(), name)))
        return cls(**values)

    def __post_init__(self):
        if any(type(v) is not int or v <= 0 for k, v in vars(self).items() if k != "seed"):
            raise UnsupportedSynthesisGoal("dp_gp limits must be positive integers")


@dataclass
class Meter:
    deadline: float
    limit: int
    nodes: int = 0

    def tick(self, count=1):
        self.nodes += count
        if self.nodes > self.limit or monotonic() >= self.deadline:
            raise SynthesisNotSuccessful("dp_gp reference/checking work or time limit exceeded")


@dataclass(frozen=True)
class Problem:
    initial: tuple[Expr, ...]
    allow: Expr
    step: tuple[Expr, ...]
    delta: tuple[Expr, ...]
    score: Expr
    base: tuple[int, ...]
    floor: int
    bounds: tuple[int, int]


@dataclass(frozen=True)
class Node:
    fuel: int
    state: tuple[int, ...]
    solutions: tuple[tuple[int, ...], ...]
    children: tuple[tuple[int, "Node"], ...]


@dataclass
class Cost:
    calls: int = 0
    cache_hits: int = 0
    retained: int = 0
    solution_cells: int = 0
    state_cells: int = 0


@dataclass(frozen=True)
class Plan:
    # Relation modes: omit, equality, >=, <=. Their conjunction is a preorder.
    relation: tuple[int, ...] = (1, 1, 1)
    solution_fields: tuple[int, ...] = (0, 1, 2)
    updates: tuple[Expr, ...] = ()
    key_fields: tuple[int, ...] = (0, 1, 2)
    state_fields: tuple[int, ...] = (0, 1, 2)


def dominates(modes, a, b):
    return all(
        mode == 0 or (x == y if mode == 1 else x >= y if mode == 2 else x <= y) for mode, x, y in zip(modes, a, b)
    )


def thin(values, relation):
    kept = []
    for value in values:
        if any(dominates(relation, old, value) for old in kept):
            continue
        kept = [old for old in kept if not dominates(relation, value, old)]
        kept.append(value)
    return tuple(kept)


def trace(problem, inputs, meter):
    def visit(fuel, state):
        meter.tick()
        if fuel == 0:
            return Node(fuel, state, (problem.base,), ())
        solutions, children = [], []
        for action in (0, 1):
            args = (*state, action)
            if problem.allow.run(args):
                child = visit(fuel - 1, tuple(e.run(args) for e in problem.step))
                children.append((action, child))
                delta = tuple(e.run(args) for e in problem.delta)
                meter.tick(len(child.solutions))
                solutions.extend(tuple(x + d for x, d in zip(p, delta)) for p in child.solutions)
        return Node(fuel, state, tuple(solutions), tuple(children))

    return visit(inputs[0], tuple(e.run(inputs) for e in problem.initial))


def nodes(root):
    yield root
    for _, child in root.children:
        yield from nodes(child)


def optimum(problem, solutions):
    return max([problem.floor, *(problem.score.run(p) for p in solutions)])


def execute(problem, root, plan=None, memoize=True):
    """Instrument the same transformations as DP.ae, independently of Aeon eval."""
    costs = Cost()
    cache = {}

    def visit(node):
        # A child state is constructed before its memo lookup, including hits.
        costs.state_cells += 3 if plan is None else len(plan.state_fields)
        key_fields = range(3) if plan is None else plan.key_fields
        key = (node.fuel, tuple(node.state[i] for i in key_fields))
        if plan is not None and memoize and key in cache:
            costs.cache_hits += 1
            return cache[key]
        costs.calls += 1
        if not node.children and node.fuel == 0:
            result = (problem.base,)
            constructed = 1
        else:
            values = []
            for action, child in node.children:
                delta = tuple(e.run((*node.state, action)) for e in problem.delta)
                for p in visit(child):
                    values.append(tuple(x + d for x, d in zip(p, delta)))
            result = tuple(values) if plan is None else thin(values, plan.relation)
            constructed = len(values)
        costs.retained += len(result)
        costs.solution_cells += constructed * (3 if plan is None else len(plan.solution_fields))
        if plan is not None and memoize:
            cache[key] = result
        return result

    values = visit(root)
    return values, costs
