"""Core LTA data structures (Definition 2 of the paper).

A Liquid Tree Automaton is a tuple A = (Q, F, Q_f, ∆) where
- Q is a set of states,
- F is a ranked alphabet (here represented implicitly by `Symbol` instances),
- Q_f ⊆ Q is the set of final states, and
- ∆ ⊆ Q^n × F × Ψ → Q is a set of constrained transitions of the form
        f(q_1,...,q_n) -ψ→ q.

Each state carries optional metadata — most importantly, an associated aeon
`Type`, which is used by the construction and similarity rules.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from itertools import count
from typing import Tuple

from aeon.core.terms import Term
from aeon.core.types import Type

from aeon.synthesis.modules.lta.constraints import CTRUE, Constraint


_state_counter = count()
_trans_counter = count()


def _fresh_state_id() -> int:
    return next(_state_counter)


def _fresh_trans_id() -> int:
    return next(_trans_counter)


# Alphabet ------------------------------------------------------------------


@dataclass(frozen=True)
class Symbol:
    """A symbol from the LTA alphabet F.

    The `kind` field discriminates between syntactic forms (variables,
    constants, applications, conditionals, type symbols, refinement-predicate
    symbols, etc.). The `payload` is symbol-specific.
    """

    kind: str
    payload: object = None
    arity: int = 0

    def __repr__(self) -> str:
        if self.payload is None:
            return self.kind
        return f"{self.kind}({self.payload!r})"


# Kinds we use throughout the implementation:
KIND_VAR = "var"  # variable / library function reference
KIND_CONST = "const"  # literal constant
KIND_APP = "app"  # function application
KIND_IF = "if"  # conditional
KIND_GOAL = "goal"  # distinguished final symbol from Q-goal
KIND_BASE_TYPE = "btype"  # primitive type marker (Int, Bool, ...)
KIND_ARROW_TYPE = "arrow"  # arrow refinement type
KIND_BASE_REF = "baseref"  # base refinement type wrapper {x:t|ϕ}
KIND_PRED = "pred"  # refinement predicate atom (ϕ ∈ Φ)
KIND_TYPE_BIND = "bind"  # bind a variable name to a refinement type
KIND_BOTTOM = "⊥"  # bottom transition (δ⊥)
# Polymorphism (Paper §3.2 footnote 5 and §5):
KIND_TYPE_ABS = "tabs"  # type abstraction  forall α:B, τ
KIND_REF_ABS = "rabs"  # refinement abstraction  forall <ρ:s→Bool>, τ
KIND_TYPE_APP = "tapp"  # type application  e[T]   (E-tapp)
KIND_TYPE_CTOR = "tctor"  # polymorphic type constructor (cyclic in qt)
KIND_PRED_AND = "pand"  # predicate conjunction (cyclic in qϕ)
KIND_PRED_OR = "por"  # predicate disjunction (cyclic in qϕ)
KIND_UNIVERSE = "univ"  # universe marker leaf (qt / qϕ bootstrap)


# States and transitions ---------------------------------------------------


@dataclass
class State:
    """An LTA state. Stores optional metadata that lets us interpret what
    the state represents — typically the aeon `Type` it accepts.

    The `is_type_state` flag marks states that live in the type sub-automaton
    (their denotation is a type structure, not an expression). Expression
    transitions skip such children when materializing terms."""

    id: int = field(default_factory=_fresh_state_id)
    label: str = ""
    aeon_type: Type | None = None
    is_type_state: bool = False

    def __hash__(self) -> int:
        return self.id

    def __eq__(self, other: object) -> bool:
        return isinstance(other, State) and self.id == other.id

    def __repr__(self) -> str:
        suffix = f":{self.aeon_type}" if self.aeon_type is not None else ""
        return f"q{self.id}({self.label}){suffix}" if self.label else f"q{self.id}{suffix}"


@dataclass
class Transition:
    """A constrained tree-automaton transition f(q_1,...,q_n) -ψ→ q."""

    symbol: Symbol
    incoming: Tuple[State, ...]
    target: State
    constraint: Constraint = CTRUE
    id: int = field(default_factory=_fresh_trans_id)

    def __hash__(self) -> int:
        return self.id

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Transition) and self.id == other.id

    def __repr__(self) -> str:
        args = ",".join(repr(s) for s in self.incoming)
        c = "" if self.constraint is CTRUE else f" -[{self.constraint}]"
        return f"{self.symbol}({args}){c}→{self.target}"


# Automaton -----------------------------------------------------------------


@dataclass
class LTA:
    states: set[State] = field(default_factory=set)
    finals: set[State] = field(default_factory=set)
    transitions: list[Transition] = field(default_factory=list)

    # Cached index: state -> list of transitions whose `target` is that state.
    _by_target: dict[int, list[Transition]] = field(default_factory=dict)

    def add_state(self, s: State) -> State:
        self.states.add(s)
        self._by_target.setdefault(s.id, [])
        return s

    def add_final(self, s: State) -> None:
        self.add_state(s)
        self.finals.add(s)

    def add_transition(self, t: Transition) -> Transition:
        for q in t.incoming:
            self.add_state(q)
        self.add_state(t.target)
        self.transitions.append(t)
        self._by_target.setdefault(t.target.id, []).append(t)
        return t

    def remove_transition(self, t: Transition) -> None:
        if t in self.transitions:
            self.transitions.remove(t)
        bucket = self._by_target.get(t.target.id, [])
        if t in bucket:
            bucket.remove(t)

    def into(self, q: State) -> list[Transition]:
        """All transitions whose target is q."""
        return list(self._by_target.get(q.id, []))

    def depth(self) -> int:
        """Maximum nesting depth of the automaton, defined as the longest
        chain of `app`/`if`/`goal` transitions reachable from a final state.
        Used by Enumerate to bound iteration."""
        memo: dict[int, int] = {}

        def go(s: State, seen: frozenset[int]) -> int:
            if s.id in memo:
                return memo[s.id]
            if s.id in seen:
                return 0  # cycle: don't recurse
            best = 0
            for t in self.into(s):
                add = 1 if t.symbol.kind in (KIND_APP, KIND_IF, KIND_GOAL) else 0
                inner = max((go(q, seen | {s.id}) for q in t.incoming), default=0)
                best = max(best, add + inner)
            memo[s.id] = best
            return best

        return max((go(f, frozenset()) for f in self.finals), default=0)


# Denotation (Fig. 6 of the paper) -----------------------------------------


def _build_term_from_trans(
    lta: LTA,
    t: Transition,
    max_terms_per_state: int,
    seen: frozenset[int],
    unroll: int,
) -> list[Term]:
    """Compute the denotation of a single transition: all aeon `Term`s that
    `t` accepts, assembled bottom-up from the denotations of its non-type
    incoming states. The cap `max_terms_per_state` keeps the cross-product
    tractable; `seen`/`unroll` bound traversal through cyclic LTAs (§5)."""
    from aeon.synthesis.modules.lta.terms import term_for_transition

    # Expression-bearing incoming states only. Type sub-automaton states are
    # carried implicitly by the transition's metadata.
    expr_children = [q for q in t.incoming if not q.is_type_state]

    if not expr_children:
        leaf = term_for_transition(t, [])
        return [] if leaf is None else [leaf]

    products: list[list[Term]] = []
    for q in expr_children:
        children = _denot_state(lta, q, max_terms_per_state, seen, unroll)
        if not children:
            return []
        products.append(children[:max_terms_per_state])

    out: list[Term] = []

    def go(idx: int, acc: list[Term]) -> None:
        if len(out) >= max_terms_per_state:
            return
        if idx == len(products):
            term = term_for_transition(t, acc)
            if term is not None:
                out.append(term)
            return
        for child in products[idx]:
            go(idx + 1, acc + [child])

    go(0, [])
    return out


# Default bound on how many times a cyclic state may be re-entered while
# materializing terms (bounded unrolling of the cyclic LTA, §5).
DEFAULT_UNROLL = 2


def _denot_state(
    lta: LTA,
    q: State,
    max_terms_per_state: int,
    seen: frozenset[int],
    unroll: int,
) -> list[Term]:
    if q.is_type_state:
        return []
    # Cycle guard: a state may be re-entered at most `unroll` times.
    if q.id in seen:
        if unroll <= 0:
            return []
        next_seen = seen
        next_unroll = unroll - 1
    else:
        next_seen = seen | {q.id}
        next_unroll = unroll
    out: list[Term] = []
    for t in lta.into(q):
        for term in _build_term_from_trans(lta, t, max_terms_per_state, next_seen, next_unroll):
            if term not in out:
                out.append(term)
                if len(out) >= max_terms_per_state:
                    return out
    return out


def denot_state(
    lta: LTA,
    q: State,
    max_terms_per_state: int = 8,
    unroll: int = DEFAULT_UNROLL,
) -> list[Term]:
    """The denotation [[q]] = union of denotations of transitions targeting q.

    Safe on cyclic LTAs: each state is re-entered at most `unroll` times."""
    return _denot_state(lta, q, max_terms_per_state, frozenset(), unroll)


def language(lta: LTA, max_terms_per_state: int = 8) -> list[Term]:
    """[[A]] = union over final states q of [[q]]."""
    out: list[Term] = []
    for f in lta.finals:
        for term in denot_state(lta, f, max_terms_per_state=max_terms_per_state):
            if term not in out:
                out.append(term)
    return out


def nonempty_finals(lta: LTA) -> list[State]:
    """NEmpty(A): final states whose denotation is non-empty."""
    return [f for f in lta.finals if denot_state(lta, f)]
