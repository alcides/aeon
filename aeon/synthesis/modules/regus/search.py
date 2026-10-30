"""Reward-guided loop-sketch MCTS with persistent execution-guided completers.

Adaptation of Cui et al., PLDI 2024. Only loop skeletons enter the high-level
tree. Each completed skeleton owns a resumable priority queue of code blocks;
conditional blocks are introduced on demand from abstract execution traces.
"""

from __future__ import annotations

import heapq
import math
import random
from collections.abc import Callable
from dataclasses import dataclass, field
from time import monotonic

from aeon.synthesis.modules.regus.model import Observation, Plan, repairs


@dataclass(frozen=True)
class Config:
    max_nodes: int = 23
    max_loops: int = 3
    max_sketch_nodes: int = 9
    max_states: int = 10000
    completion_batch: int = 2
    exploration: float = 0.7
    structure_cost: float = 0.01
    evaluation_timeout: float = 5.0

    def __post_init__(self):
        if (
            min(self.max_nodes, self.max_sketch_nodes, self.max_states, self.completion_batch) <= 0
            or self.max_loops < 0
        ):
            raise ValueError("ReGuS search limits must be positive (max_loops may be zero)")
        if not all(math.isfinite(x) and x >= 0 for x in (self.exploration, self.structure_cost)):
            raise ValueError("ReGuS exploration and structure cost must be finite and nonnegative")
        if not math.isfinite(self.evaluation_timeout) or self.evaluation_timeout <= 0:
            raise ValueError("ReGuS evaluation timeout must be finite and positive")


@dataclass
class Stats:
    assessments: int = 0
    sketches: int = 0
    sketch_revisits: int = 0
    branches: int = 0
    invalid: int = 0
    complete: int = 0
    backpropagations: int = 0


@dataclass
class Node:
    sketch: Plan
    visits: int = 0
    total: float = 0.0
    children: list[Node] | None = None
    exhausted: bool = False


@dataclass
class Completion:
    queue: list[tuple[float, int, Plan]] = field(default_factory=list)
    repair_queue: list[tuple[float, int, Plan]] = field(default_factory=list)
    seen: set[Plan] = field(default_factory=set)
    visits: int = 0
    best_complete: float = -1e6
    turns: int = 0


def utility(values: list[float], minimize: list[bool]) -> float:
    if len(values) != len(minimize) or not values or not all(math.isfinite(v) for v in values):
        raise ValueError("ReGuS needs finite scores matching the declared objectives")
    # Monotone compression lets UCT handle arbitrary reward/loss scales and
    # signs. It affects scheduling only; final Pareto acceptance is unchanged.
    oriented = [v if m else -v for v, m in zip(values, minimize)]
    return -sum(math.copysign(math.log1p(abs(v)), v) for v in oriented) / len(oriented)


def sketch_successors(plan: Plan, predicates: int, config: Config) -> list[Plan]:
    paths = plan.paths("sketch")
    if not paths:
        return []
    pc = paths[0]
    replacements = [Plan("gap")]
    loops = len(plan.paths("loop"))
    if loops < config.max_loops:
        replacements.extend(Plan("loop", i, (Plan("sketch"),)) for i in range(predicates))
    replacements.append(Plan("sequence", children=(Plan("sketch"), Plan("sketch"))))
    return [p for r in replacements if (p := plan.replace(pc, r)).size <= config.max_sketch_nodes]


def code_successors(plan: Plan, observation: Observation, skills: tuple[Plan, ...]) -> list[Plan]:
    paths = plan.paths("gap")
    if not paths:
        return []
    # Expand the first actually reached gap, then close unreachable code.
    reached = [ep.blocked for ep in observation.episodes if ep.blocked in paths]
    pc = reached[0] if reached else paths[0]
    atoms = [Plan("action", i) for i in range(observation.actions)] + list(skills)
    replacements = [Plan("halt"), *atoms]
    replacements.extend(Plan("sequence", children=(atom, Plan("gap"))) for atom in atoms)
    return [plan.replace(pc, replacement) for replacement in replacements]


def search(
    assess: Callable[[Plan], tuple[float, Observation] | None],
    observation: Observation,
    *,
    seed: int,
    budget: float,
    config: Config,
    stats: Stats,
    skills: tuple[Plan, ...] = (),
) -> None:
    rng = random.Random(seed)
    deadline = monotonic() + max(0.0, budget)
    root = Node(Plan("sketch"))
    queues: dict[Plan, Completion] = {}
    measured: dict[Plan, tuple[float, Observation] | None] = {}
    serial = 0
    tree_nodes = 1

    def measure(plan: Plan) -> tuple[float, Observation] | None:
        if plan not in measured:
            if monotonic() >= deadline or len(measured) >= config.max_states:
                return None
            measured[plan] = assess(plan)
        return measured[plan]

    def add(queue: Completion, plan: Plan) -> None:
        nonlocal serial
        if plan in queue.seen or plan.size > config.max_nodes or len(queue.seen) >= config.max_states:
            return
        queue.seen.add(plan)
        result = measure(plan)
        if result is not None:
            quality, observation = result
            if not plan.contains("gap") and observation.closed:
                queue.best_complete = max(queue.best_complete, quality)
            serial += 1
            destination = queue.repair_queue if plan.contains("branch") else queue.queue
            heapq.heappush(destination, (-quality + config.structure_cost * plan.size, serial, plan))
            # Execution discovers the disagreement now. Waiting until a
            # completed program is popped can starve all conditional repairs
            # behind arbitrarily many cheap, short incomplete prefixes.
            if not plan.contains("gap"):
                for proposal in repairs(plan, observation):
                    if proposal not in queue.seen:
                        stats.branches += 1
                        add(queue, proposal)
                    if monotonic() >= deadline:
                        break

    def complete(sketch: Plan) -> float:
        if sketch not in queues:
            queues[sketch] = Completion()
            stats.sketches += 1
            add(queues[sketch], sketch)
        queue = queues[sketch]
        stats.sketch_revisits += int(queue.visits > 0)
        queue.visits += 1
        for _ in range(config.completion_batch):
            if not (queue.queue or queue.repair_queue) or monotonic() >= deadline:
                break
            # Give on-demand repair and ordinary block completion fair turns.
            # Both queues retain the reward/size ordering and survive revisits.
            pending = (
                queue.repair_queue if queue.repair_queue and (queue.turns % 2 == 0 or not queue.queue) else queue.queue
            )
            queue.turns += 1
            _, _, plan = heapq.heappop(pending)
            result = measured[plan]
            assert result is not None
            quality, trace = result
            if not plan.contains("gap") and trace.closed:
                queue.best_complete = max(queue.best_complete, quality)
            for proposal in code_successors(plan, trace, skills):
                add(queue, proposal)
                if monotonic() >= deadline:
                    break
            for proposal in repairs(plan, trace):
                if proposal not in queue.seen:
                    stats.branches += 1
                    add(queue, proposal)
                if monotonic() >= deadline:
                    break
        return queue.best_complete

    while not root.exhausted and monotonic() < deadline and len(measured) < config.max_states:
        node = root
        path = [node]
        while node.sketch.contains("sketch"):
            if node.children is None:
                successors = sketch_successors(node.sketch, observation.predicates, config)
                if tree_nodes + len(successors) > config.max_states:
                    return
                node.children = [Node(p) for p in successors]
                tree_nodes += len(node.children)
            available = [child for child in node.children if not child.exhausted]
            if not available:
                node.exhausted = True
                break
            unvisited = [child for child in available if child.visits == 0]
            if unvisited:
                # Try shallow skeletons before spending a rollout completing
                # a random nest of loops. Sensor indices retain source order.
                node = min(unvisited, key=lambda child: child.sketch.size)
            else:

                def uct(child: Node) -> float:
                    return child.total / child.visits + config.exploration * math.sqrt(
                        math.log(max(1, node.visits)) / child.visits
                    )

                scores = [(uct(child), child) for child in available]
                maximum = max(score for score, _ in scores)
                node = rng.choice([child for score, child in scores if score == maximum])
            path.append(node)
        reward = complete(node.sketch) if not node.sketch.contains("sketch") else -1e6
        if node.sketch in queues:
            node.exhausted = not (queues[node.sketch].queue or queues[node.sketch].repair_queue)
        for visited in path:
            visited.visits += 1
            visited.total += reward
            stats.backpropagations += 1
