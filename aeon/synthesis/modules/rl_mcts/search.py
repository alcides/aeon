"""Monte-Carlo grammar tree search, algorithms 1/2 and section 3.2.

No simulation to a random leaf: expansions are evaluated by a value predictor,
and only complete grammar terms are sent to the correctness oracle.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field
from math import isfinite, log, sqrt
import random
from time import monotonic
from typing import Generic, Protocol, TypeVar

from aeon.synthesis.modules.rl_mcts.features import Syntax

S = TypeVar("S")


class Guidance(Protocol):
    def value(self, spec: Syntax, state: Syntax, holes: int) -> float: ...

    def policy(self, spec: Syntax, state: Syntax, child: Syntax) -> float: ...


class DefaultGuidance:
    def value(self, spec: Syntax, state: Syntax, holes: int) -> float:
        return 0.95**holes

    def policy(self, spec: Syntax, state: Syntax, child: Syntax) -> float:
        return 1.0


@dataclass(frozen=True)
class SearchConfig:
    big_steps: int = 30
    rollouts: int = 6500
    exploration: float = 1.0
    decay: float = 0.98
    max_nodes: int = 100_000

    def __post_init__(self) -> None:
        if self.big_steps < 1 or self.rollouts < 1 or self.max_nodes < 1:
            raise ValueError("search limits must be positive")
        if not isfinite(self.exploration) or self.exploration < 0:
            raise ValueError("exploration must be finite and nonnegative")
        if not isfinite(self.decay) or not 0 < self.decay <= 1:
            raise ValueError("decay must be in (0, 1]")


@dataclass(eq=False)
class Node(Generic[S]):
    state: S
    tree: Syntax
    holes: int
    parent: Node[S] | None = None
    prior: float = 1.0
    visits: int = 0
    total: float = 0.0
    expanded: bool = False
    exhausted: bool = False
    children: list[Node[S]] = field(default_factory=list)

    def path(self) -> list[Node[S]]:
        result: list[Node[S]] = []
        current: Node[S] | None = self
        while current is not None:
            result.append(current)
            current = current.parent
        return list(reversed(result))


def uct(parent: Node[S], child: Node[S], exploration: float = 1.0) -> float:
    # Force each child to be visited, including children assigned zero prior.
    if child.visits == 0:
        return float("inf")
    return child.total / child.visits + exploration * child.prior * sqrt(log(max(1, parent.visits)) / child.visits)


@dataclass
class SearchResult(Generic[S]):
    root: Node[S]
    solution: Node[S] | None
    nodes: list[Node[S]]
    reason: str


def bounded_prediction(value: float) -> float:
    if not isfinite(value):
        raise ValueError("guidance returned a non-finite prediction")
    return min(1.0, max(0.0, value))


def search(
    initial: S,
    spec: Syntax,
    describe: Callable[[S], Syntax],
    holes: Callable[[S], int],
    expand: Callable[[S], list[S]],
    verify: Callable[[S], bool],
    *,
    guidance: Guidance | None = None,
    config: SearchConfig = SearchConfig(),
    budget: float = 60,
    seed: int = 0,
) -> SearchResult[S]:
    guidance = guidance or DefaultGuidance()
    rng = random.Random(seed)
    deadline = monotonic() + max(0.0, budget)
    root = Node(initial, describe(initial), holes(initial))
    nodes = [root]
    active = root

    def best(children: list[Node[S]], score: Callable[[Node[S]], float]) -> Node[S]:
        scores = [(child, score(child)) for child in children]
        maximum = max(v for _, v in scores)
        return rng.choice([c for c, v in scores if v == maximum])

    for step in range(config.big_steps):
        for _ in range(config.rollouts):
            if monotonic() >= deadline:
                return SearchResult(root, None, nodes, "timeout")
            node = active
            path = [node]
            while node.expanded and not node.exhausted:
                available = [c for c in node.children if not c.exhausted]
                if not available:
                    node.exhausted = True
                    break
                node = best(available, lambda c: uct(node, c, config.exploration))
                path.append(node)
            reward = 0.0
            if not node.exhausted:
                if node.holes == 0:
                    if verify(node.state):
                        # Record the successful terminal visit for policy labels.
                        for visited in path:
                            visited.visits += 1
                        return SearchResult(root, node, nodes, "solved")
                    node.exhausted = True
                else:
                    successors = expand(node.state)
                    if monotonic() >= deadline:
                        return SearchResult(root, None, nodes, "timeout")
                    if len(nodes) + len(successors) > config.max_nodes:
                        return SearchResult(root, None, nodes, "node limit")
                    for state in successors:
                        if monotonic() >= deadline:
                            return SearchResult(root, None, nodes, "timeout")
                        tree = describe(state)
                        prior = bounded_prediction(guidance.policy(spec, node.tree, tree))
                        child = Node(state, tree, holes(state), parent=node, prior=prior)
                        node.children.append(child)
                        nodes.append(child)
                    node.expanded = True
                    node.exhausted = not bool(node.children)
                    if not node.exhausted:
                        reward = bounded_prediction(guidance.value(spec, node.tree, node.holes))
            for visited in path:
                visited.visits += 1
                visited.total += reward * config.decay**step
            if active.exhausted:
                return SearchResult(root, None, nodes, "exhausted")
        available = [c for c in active.children if not c.exhausted]
        if not available:
            return SearchResult(root, None, nodes, "exhausted")
        active = best(available, lambda c: float(c.visits))
    return SearchResult(root, None, nodes, "big-step limit")
