"""Controller syntax and the language-neutral abstract execution protocol."""

from __future__ import annotations

from dataclasses import dataclass
from math import isfinite

from aeon.core.terms import Application, Literal, Term, Var
from aeon.core.types import t_int
from aeon.utils.name import Name


@dataclass(frozen=True)
class Plan:
    kind: str
    argument: int = 0
    children: tuple[Plan, ...] = ()
    skill: Name | None = None

    @property
    def size(self) -> int:
        return 1 + sum(child.size for child in self.children)

    def contains(self, kind: str) -> bool:
        return self.kind == kind or any(child.contains(kind) for child in self.children)

    def paths(self, kind: str, pc: int = 1) -> list[int]:
        return ([pc] if self.kind == kind else []) + [
            path for i, child in enumerate(self.children) for path in child.paths(kind, 2 * pc + i)
        ]

    def at(self, pc: int) -> Plan:
        result = self
        for bit in bin(pc)[3:]:
            result = result.children[int(bit)]
        return result

    def replace(self, pc: int, replacement: Plan) -> Plan:
        bits = bin(pc)[3:]

        def visit(plan: Plan, index: int) -> Plan:
            if index == len(bits):
                return replacement
            position = int(bits[index])
            children = list(plan.children)
            children[position] = visit(children[position], index + 1)
            return Plan(plan.kind, plan.argument, tuple(children), plan.skill)

        return visit(self, 0)

    def term(self, constructors: dict[str, Name]) -> Term:
        if self.kind == "skill":
            assert self.skill is not None
            return Var(self.skill)
        result: Term = Var(constructors[self.kind])
        if self.kind in {"action", "loop", "branch"}:
            result = Application(result, Literal(self.argument, t_int))
        for child in self.children:
            result = Application(result, child.term(constructors))
        return result


@dataclass(frozen=True)
class Event:
    pc: int
    action: int
    before: int
    after: int


@dataclass(frozen=True)
class Episode:
    blocked: int
    steps: int
    failed: bool
    loss: float
    events: tuple[Event, ...]


@dataclass(frozen=True)
class Observation:
    actions: int
    predicates: int
    episodes: tuple[Episode, ...]
    closed: bool = True

    def value(self, mask: int, predicate: int) -> bool:
        # ControlTask.mask_from stores predicate zero in the highest bit.
        return bool(mask & (1 << (self.predicates - predicate - 1)))


def decode(value: object) -> Observation:
    """Check the complete protocol before interpreting user-supplied features."""

    def fields(node: object, tag: str, arity: int) -> tuple:
        if type(node) is not tuple or len(node) != arity + 1 or node[0] != tag:
            raise ValueError(f"expected {tag} with {arity} fields")
        return node[1:]

    def integer(n: object, low: int, high: int) -> int:
        if type(n) is not int or not low <= n <= high:
            raise ValueError("out-of-range control observation integer")
        return n

    actions, predicates, seeds, closed, reports = fields(value, "ControlObservation_snapshot", 5)
    actions = integer(actions, 1, 32)
    predicates = integer(predicates, 1, 16)
    seeds = integer(seeds, 1, 32)
    if type(closed) is not bool:
        raise ValueError("invalid controller closedness flag")
    episodes = []
    for _ in range(seeds):
        blocked, steps, failed, loss, trace, reports = fields(reports, "ControlReport_episode", 6)
        blocked = integer(blocked, 0, 2**32)
        steps = integer(steps, 0, 500)
        if type(failed) is not bool or type(loss) not in (int, float) or not isfinite(loss):
            raise ValueError("invalid episode status or loss")
        events = []
        for _ in range(501):
            if trace == ("ControlTrace_empty",):
                break
            pc, action, before, after, trace = fields(trace, "ControlTrace_event", 5)
            events.append(
                Event(
                    integer(pc, 1, 2**32),
                    integer(action, 0, actions - 1),
                    integer(before, 0, 2**predicates - 1),
                    integer(after, 0, 2**predicates - 1),
                )
            )
        else:
            raise ValueError("execution trace exceeds 500 actions")
        if len(events) != steps:
            raise ValueError("execution trace does not match step count")
        episodes.append(Episode(blocked, steps, failed, float(loss), tuple(reversed(events))))
    fields(reports, "ControlReport_empty", 0)
    return Observation(actions, predicates, tuple(episodes), closed)


def repairs(plan: Plan, observation: Observation) -> list[Plan]:
    """Lazy branch proposals at observed action-precondition disagreements.

    An action site initially assumes its first abstract pre-state. A later
    disagreement identifies a sensor predicate that separates the contexts.
    Keep the known action on its original branch and open the other branch.
    Post-state agreement orders proposals toward branches that can rejoin.
    These are empirical contracts; final acceptance still uses real fitness.
    """
    contracts: dict[int, Event] = {}
    proposals: dict[Plan, int] = {}
    for episode in observation.episodes:
        for event in episode.events:
            if event.pc not in contracts:
                contracts[event.pc] = event
                continue
            first = contracts[event.pc]
            if first.before == event.before:
                continue
            try:
                original = plan.at(event.pc)
            except IndexError:
                # A supplied procedure's internal PCs are opaque to this AST.
                continue
            if original.kind != "action":
                continue
            for predicate in range(observation.predicates):
                old = observation.value(first.before, predicate)
                if old == observation.value(event.before, predicate):
                    continue
                branch = Plan("branch", predicate, (original, Plan("gap")) if old else (Plan("gap"), original))
                proposal = plan.replace(event.pc, branch)
                proposals[proposal] = max(proposals.get(proposal, 0), int(first.after == event.after))
    return sorted(proposals, key=lambda p: -proposals[p])
