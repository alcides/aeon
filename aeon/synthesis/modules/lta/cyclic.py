"""Cyclic LTA structure for polymorphic types and abstract refinements
(Paper §5).

Precisely capturing parametric polymorphism and abstract refinements requires
*cyclic* edges in the LTA:

  - A universe state `qt` captures all valid base-refinement types. A
    polymorphic type constructor (e.g. `List α`) is modelled by a transition
    whose argument position points back at `qt` — a cycle.
  - A universe state `qϕ` captures all valid refinement predicates: atomic
    predicates, method predicates `Q(ν)`, and `∧`/`∨` of other predicates
    (the latter introduce cycles from `qϕ` to itself).

Cycles compactly represent an unbounded sequence of types/refinements. To keep
SMT queries tractable, the paper imposes a structural restriction — *the
acyclic-constraint restriction*: a transition's position constraints may not
refer to a state that participates in a cycle. This module provides:

  - `build_type_universe`     — constructs `qt` with cyclic constructor edges.
  - `build_predicate_universe`— constructs `qϕ` with cyclic ∧/∨ edges.
  - `DependencyGraph` + `find_cycle_states` — SCC analysis over an LTA.
  - `well_formed_constraints` — checks the acyclic-constraint restriction.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from aeon.core.types import Type
from aeon.typechecking.context import TypeConstructorBinder, TypingContext

from aeon.synthesis.modules.lta.automaton import (
    KIND_BASE_TYPE,
    KIND_PRED,
    KIND_PRED_AND,
    KIND_PRED_OR,
    KIND_TYPE_CTOR,
    LTA,
    State,
    Symbol,
    Transition,
)
from aeon.synthesis.modules.lta.constraints import CTRUE


# Universe construction (§5) ------------------------------------------------


@dataclass
class Universe:
    """Handle on the cyclic universe states of an LTA."""

    qt: State  # universe of base-refinement types
    qphi: State  # universe of refinement predicates


def build_type_universe(
    lta: LTA,
    ctx: TypingContext,
    concrete_types: list[Type],
) -> State:
    """Construct the cyclic universe state `qt`.

    For each concrete base type we add a nullary transition `t() → qt`. For
    each *polymorphic* type constructor in the context (arity ≥ 1) we add a
    transition `C(qt, ..., qt) → qt` — the cyclic edge that lets `C` be
    instantiated at any type, including itself.
    """
    qt = State(label="qt:universe", is_type_state=True)
    lta.add_state(qt)

    # Concrete base types — bounded unrolling targets.
    for ty in concrete_types:
        lta.add_transition(
            Transition(
                symbol=Symbol(KIND_BASE_TYPE, payload=str(ty), arity=0),
                incoming=(),
                target=qt,
            )
        )

    # Polymorphic constructors — cyclic edges back into qt.
    for entry in ctx.entries:
        if isinstance(entry, TypeConstructorBinder) and entry.args:
            arity = len(entry.args)
            lta.add_transition(
                Transition(
                    symbol=Symbol(KIND_TYPE_CTOR, payload=entry.name, arity=arity),
                    incoming=tuple(qt for _ in range(arity)),  # cycle: qt → qt
                    target=qt,
                )
            )
    return qt


# Standard atomic predicates seeded into the predicate universe (§5 mentions
# "standard predicates like {ν ≥ 0, ν < 0, ...}").
DEFAULT_ATOMIC_PREDICATES = ("ν ≥ 0", "ν < 0", "ν = 0", "true")


def build_predicate_universe(
    lta: LTA,
    atomic_predicates: tuple[str, ...] = DEFAULT_ATOMIC_PREDICATES,
) -> State:
    """Construct the cyclic universe state `qϕ`.

    Seeds atomic predicate leaves, then adds binary `∧`/`∨` transitions whose
    incoming states are `qϕ` itself — the cyclic edges of §5.
    """
    qphi = State(label="qϕ:universe", is_type_state=True)
    lta.add_state(qphi)

    for pred in atomic_predicates:
        lta.add_transition(
            Transition(
                symbol=Symbol(KIND_PRED, payload=pred, arity=0),
                incoming=(),
                target=qphi,
            )
        )

    # Cyclic ∧ / ∨ over predicates.
    lta.add_transition(
        Transition(
            symbol=Symbol(KIND_PRED_AND, arity=2),
            incoming=(qphi, qphi),
            target=qphi,
        )
    )
    lta.add_transition(
        Transition(
            symbol=Symbol(KIND_PRED_OR, arity=2),
            incoming=(qphi, qphi),
            target=qphi,
        )
    )
    return qphi


def build_universe(
    lta: LTA,
    ctx: TypingContext,
    concrete_types: list[Type],
) -> Universe:
    """Build both cyclic universe states and return a handle on them."""
    qt = build_type_universe(lta, ctx, concrete_types)
    qphi = build_predicate_universe(lta)
    return Universe(qt=qt, qphi=qphi)


# Dependency graph & cycle detection (§5) ----------------------------------


@dataclass
class DependencyGraph:
    """The dependency graph of an LTA: a node per state, with an edge
    q → q' whenever q' is an incoming state of some transition targeting q
    (i.e. building a term at q depends on building one at q')."""

    adj: dict[int, set[int]] = field(default_factory=dict)
    states: dict[int, State] = field(default_factory=dict)

    @staticmethod
    def from_lta(lta: LTA) -> "DependencyGraph":
        g = DependencyGraph()
        for s in lta.states:
            g.adj.setdefault(s.id, set())
            g.states[s.id] = s
        for t in lta.transitions:
            g.adj.setdefault(t.target.id, set())
            for q in t.incoming:
                g.adj[t.target.id].add(q.id)
                g.adj.setdefault(q.id, set())
        return g


def find_cycle_states(lta: LTA) -> set[int]:
    """Return the ids of states that participate in a cycle of the LTA's
    dependency graph — i.e. members of a non-trivial strongly-connected
    component, plus any state with a self-loop.

    Uses an iterative Tarjan SCC to stay safe on large automata.
    """
    g = DependencyGraph.from_lta(lta)
    index_counter = [0]
    index: dict[int, int] = {}
    lowlink: dict[int, int] = {}
    on_stack: dict[int, bool] = {}
    stack: list[int] = []
    cycle_states: set[int] = set()

    for root in list(g.adj.keys()):
        if root in index:
            continue
        # Iterative DFS.
        work: list[tuple[int, int]] = [(root, 0)]
        while work:
            node, pi = work[-1]
            if pi == 0:
                index[node] = lowlink[node] = index_counter[0]
                index_counter[0] += 1
                stack.append(node)
                on_stack[node] = True
            recursed = False
            neighbours = sorted(g.adj.get(node, set()))
            if pi < len(neighbours):
                work[-1] = (node, pi + 1)
                w = neighbours[pi]
                if w not in index:
                    work.append((w, 0))
                    recursed = True
                elif on_stack.get(w, False):
                    lowlink[node] = min(lowlink[node], index[w])
            if recursed:
                continue
            if pi >= len(neighbours):
                if lowlink[node] == index[node]:
                    # Pop an SCC.
                    scc: list[int] = []
                    while True:
                        w = stack.pop()
                        on_stack[w] = False
                        scc.append(w)
                        if w == node:
                            break
                    if len(scc) > 1:
                        cycle_states.update(scc)
                    elif node in g.adj.get(node, set()):
                        cycle_states.add(node)  # self-loop
                work.pop()
                if work:
                    parent = work[-1][0]
                    lowlink[parent] = min(lowlink[parent], lowlink[node])
    return cycle_states


# Acyclic-constraint restriction (§5) --------------------------------------


def _states_constrained_by(lta: LTA, t: Transition) -> set[int]:
    """The set of state ids that the constraint of transition `t` may refer
    to. In this implementation every constraint relates positions rooted at
    `t`'s own incoming states, so the referenced set is the transitive
    closure of those incoming states (following transitions backward)."""
    if t.constraint is CTRUE:
        return set()
    referenced: set[int] = set()
    worklist: list[State] = list(t.incoming)
    while worklist:
        s = worklist.pop()
        if s.id in referenced:
            continue
        referenced.add(s.id)
        for inc_t in lta.into(s):
            worklist.extend(inc_t.incoming)
    return referenced


def well_formed_constraints(lta: LTA) -> tuple[bool, list[str]]:
    """Check the acyclic-constraint restriction of §5: no transition's
    position constraints may refer to a state that participates in a cycle.

    Returns `(ok, violations)` where `violations` describes each offending
    transition. This is a conservative check — it considers the full set of
    states reachable from a constrained transition's incoming states, which
    in this implementation is exactly the set its constraints range over.
    """
    cycle_states = find_cycle_states(lta)
    if not cycle_states:
        return True, []
    violations: list[str] = []
    for t in lta.transitions:
        if t.constraint is CTRUE:
            continue
        referenced = _states_constrained_by(lta, t)
        bad = referenced & cycle_states
        if bad:
            violations.append(
                f"transition {t.symbol} → q{t.target.id} constrains cycle state(s) "
                + ", ".join(f"q{i}" for i in sorted(bad))
            )
    return (not violations), violations
