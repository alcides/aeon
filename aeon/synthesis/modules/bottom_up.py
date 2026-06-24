"""Shared bottom-up skeleton for the tree-automata synthesis backends.

The ``fta``, ``afta`` and ``cata`` backends all build candidate programs
bottom-up over an in-scope component bank: round 0 seeds nullary leaves, and
each later round applies every component-transition to the bank grown so far,
deepening the programs by one operator. They share four genuinely-identical
pieces, collected here so the three backends stop copy-pasting them:

* ``Component`` -- a ranked transition label (a head ``Term`` plus the base-type
  keys of its arguments and result), generic enough to carry a plain ``Var``
  head (fta/afta) or a type-applied / monomorphised head (cata, and fta's
  polymorphic operators);
* ``combos`` -- the product-or-sample enumeration of a transition's
  applications over the bank (full product when small, else a bounded random
  sample), parameterised by the term builder so each backend keeps its own node
  construction;
* ``deepen`` -- the round-deepening loop's bookkeeping (snapshot the bank, run
  the per-round step, stop on success / deadline / depth cap / bank fixpoint);
* ``safe`` / ``term_size`` / ``freeze`` -- the validate-with-guard, size measure
  and hashable-output helpers.

What is *not* unified: component collection (``_collect``) stays per-backend --
the signatures and instantiation policies genuinely differ (fta monomorphises
operators itself at the goal type, afta skips polymorphic bindings entirely, and
cata monomorphises via the ``lta`` universe). Forcing those together would
change which components each search sees.
"""

from __future__ import annotations

import itertools
import random
import time
from dataclasses import dataclass, field
from typing import Any, Callable, Protocol, TypeVar

from aeon.core.terms import Application, Term
from aeon.synthesis.modules.symetric.synthesizer import _decompose


class _HasArgKeys(Protocol):
    @property
    def arg_keys(self) -> tuple[str, ...]: ...


C = TypeVar("C", bound=_HasArgKeys)


@dataclass(frozen=True)
class Component:
    """A ranked transition ``head(q1, ..., qk) -> q`` of the tree automaton: a
    head term -- ``Var(f)`` for a monomorphic binding, or a ``TypeApplication``
    nest for a polymorphic operator instantiated at concrete types -- with the
    base-type keys of its arguments and result.

    ``is_if`` marks the conditional builder ``If(cond, then, else)``, whose
    construction the backends supply themselves (the head is then unused)."""

    head: Term
    arg_keys: tuple[str, ...]
    ret_key: str
    is_if: bool = False
    # Backend-specific extras carried alongside the transition (e.g. fta tags
    # each component with the concrete argument types it was instantiated at);
    # never inspected here, only by the owning backend.
    extra: Any = field(default=None, compare=False)


def application(head: Term, args: tuple[Term, ...]) -> Term:
    """Left-fold ``head`` over ``args`` into a curried application."""
    term = head
    for a in args:
        term = Application(term, a)
    return term


def combos(
    comp: C,
    bank: dict[str, list[Term]],
    deadline: float,
    rnd: random.Random,
    combo_cap: int,
    build: Callable[[C, tuple[Term, ...]], Term],
    *,
    pool_for: Callable[[int, str, list[Term]], list[Term]] | None = None,
    cap_for: Callable[[C, int], int] | None = None,
) -> list[Term]:
    """Transitions ``comp(q1, ..., qk) -> q``: build ``comp`` over arguments
    drawn from the current bank (one pool per argument key). Enumerate the full
    product when it fits within the cap, else draw ``cap`` random samples of it.

    ``build`` turns a chosen argument tuple into a term -- the only backend
    variation in the common case. ``pool_for`` may restrict / reorder a pool by
    argument position (fta's then/else branch cap); ``cap_for`` may raise the cap
    for a given transition (fta enumerates the bounded conditional fully)."""
    pools: list[list[Term]] = []
    for idx, ak in enumerate(comp.arg_keys):
        pool = bank.get(ak, [])
        if not pool:
            return []
        if pool_for is not None:
            pool = pool_for(idx, ak, pool)
        pools.append(pool)
    total = 1
    for p in pools:
        total *= len(p)
    cap = cap_for(comp, total) if cap_for is not None else combo_cap

    out: list[Term] = []
    if total <= cap:
        for choice in itertools.product(*pools):
            if time.time() >= deadline:
                break
            out.append(build(comp, choice))
    else:
        for _ in range(cap):
            out.append(build(comp, tuple(rnd.choice(p) for p in pools)))
    return out


def deepen(
    bank: dict[str, list[Term]],
    deadline: float,
    rounds: int | None,
    found: Callable[[], bool],
    step: Callable[[dict[str, list[Term]]], None],
) -> int:
    """Run the round-deepening loop over ``bank`` and return the depth reached.

    Each round snapshots the bank, runs ``step`` (the backend's per-round growth
    over that snapshot), and stops when a solution is found, the deadline passes,
    the explicit ``rounds`` depth cap is hit, or the bank reaches a fixpoint (a
    full round adds no new terms). ``step`` mutates ``bank`` in place and is the
    only backend-specific part; ``found`` reports whether a solution now exists.

    Mirrors the bottom-up bound shared by fta/afta/cata: depth is governed by the
    time budget, not a fixed round count, so the search reaches the smallest
    programs first and only deepens while shallower depths are dry."""
    depth = 0
    while not found() and time.time() < deadline:
        if rounds is not None and depth >= rounds:
            break
        before = sum(len(v) for v in bank.values())
        snapshot = {k: list(v) for k, v in bank.items()}
        step(snapshot)
        depth += 1
        if sum(len(v) for v in bank.values()) == before:
            break
    return depth


def term_size(term: Term) -> int:
    """Node count of a term -- the size measure minimised during extraction."""
    _head, args = _decompose(term)
    return 1 + sum(term_size(a) for a in args)


def freeze(v: object) -> Any:
    """A hashable, order-stable view of a candidate's output, so that equal
    outputs map to the same automaton state regardless of container type."""
    if isinstance(v, (list, tuple)):
        return tuple(freeze(x) for x in v)
    if isinstance(v, (set, frozenset)):
        return frozenset(freeze(x) for x in v)
    if isinstance(v, dict):
        return tuple(sorted((k, freeze(x)) for k, x in v.items()))
    return v


def safe(validate: Callable[[Term], bool], term: Term) -> bool:
    """Run ``validate`` on ``term``, treating any exception as rejection."""
    try:
        return validate(term)
    except Exception:
        return False
