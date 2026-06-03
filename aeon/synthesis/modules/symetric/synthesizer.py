"""SyMetric: metric program synthesis, as an aeon ``Synthesizer`` backend.

Implements the approach of Feser, Dillig & Solar-Lezama, "Metric Program
Synthesis for Inverse CSG" (arXiv:2206.06164). Where the other backends use
observational *equivalence*, metric synthesis is guided by a distance *metric*
on outputs: programs whose outputs are close to the goal are good, and the
search drives that distance to zero.

The aeon synthesis interface already exposes exactly the metric we need:
``evaluate(term) -> list[float]`` is the fitness/distance of a candidate (e.g.
the Jaccard distance of the inverse-CSG benchmarks), and ``validate(term)``
checks well-typedness. This backend therefore implements the paper's pipeline
directly over that interface:

1. **Construct** an (approximate) version space by sampling well-typed
   candidate programs bottom-up from the library components in scope (the
   inductive constructors, library functions and constants).
2. **Cluster** candidates by their metric value, keeping a diverse set of
   low-distance representatives -- the compression that makes the version
   space of "approximately correct" programs small.
3. **Extract** the representative closest to the goal.
4. **Repair** it with distance-guided local search: perturb numeric constants
   and regenerate sub-terms, accepting improvements (with a patience/tabu
   cutoff and restarts from other representatives), until the metric reaches 0
   -- an exact reconstruction, which is then validated -- or the budget ends.

It targets single-metric *minimization* problems (the paper's setting). When a
hole carries no ``@minimize``/``@maximize`` objective the metric is absent, and
the backend degrades to a plain search for any well-typed term.

Selected with ``--synthesizer symetric``.
"""

from __future__ import annotations

import random
import time
from dataclasses import dataclass
from typing import Callable, Optional

from loguru import logger

from aeon.core.terms import Application, Literal, Term, Var
from aeon.core.types import (
    AbstractionType,
    RefinedType,
    Type,
    TypeConstructor,
    TypePolymorphism,
    TypeVar,
    t_int,
)
from aeon.decorators.api import Metadata
from aeon.synthesis.api import (
    InvalidIndividualException,
    SynthesisError,
    Synthesizer,
    SynthesisNotSuccessful,
)
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name

INF = float("inf")


def base_key(ty: Type) -> str:
    """A coarse, refinement-agnostic key identifying a type's base shape."""
    while isinstance(ty, RefinedType):
        ty = ty.type
    if isinstance(ty, TypeConstructor):
        return ty.name.name
    if isinstance(ty, TypeVar):
        return ty.name.name
    return str(ty)


@dataclass(frozen=True)
class Component:
    """A library function/constructor usable to build candidate terms."""

    name: Name
    arg_keys: tuple[str, ...]
    ret_key: str

    @property
    def is_recursive_in(self) -> Callable[[str], bool]:
        return lambda k: k in self.arg_keys


def _peel(ty: Type) -> tuple[list[Type], Type]:
    """Split a (possibly multi-argument) function type into args and result."""
    args: list[Type] = []
    cur = ty
    while isinstance(cur, AbstractionType):
        args.append(cur.var_type)
        cur = cur.type
    return args, cur


class SymetricSynthesizer(Synthesizer):
    def __init__(
        self,
        seed: int = 0,
        int_lo: int = 0,
        int_hi: int = 16,
        pool: int = 256,
        patience: int = 64,
        max_arg_depth: int = 2,
        construct_fraction: float = 0.35,
    ):
        self.seed = seed
        self.int_lo = int_lo
        self.int_hi = int_hi
        self.pool = pool
        self.patience = patience
        self.max_arg_depth = max_arg_depth
        self.construct_fraction = construct_fraction

    # -- term construction ----------------------------------------------------

    def _collect(self, ctx: TypingContext) -> tuple[dict[str, list[Component]], dict[str, list[Var]]]:
        """Index the in-scope bindings as constructors (functions) and atoms."""
        builders: dict[str, list[Component]] = {}
        atoms: dict[str, list[Var]] = {}
        for name, ty in ctx.concrete_vars():
            if isinstance(ty, TypePolymorphism):
                continue  # recursors / polymorphic library functions
            arg_types, ret = _peel(ty)
            if any(isinstance(a, (AbstractionType, TypePolymorphism)) for a in arg_types):
                continue  # no higher-order arguments
            if isinstance(ret, (AbstractionType, TypePolymorphism)):
                continue
            ret_key = base_key(ret)
            if arg_types:
                comp = Component(name, tuple(base_key(a) for a in arg_types), ret_key)
                builders.setdefault(ret_key, []).append(comp)
            else:
                atoms.setdefault(ret_key, []).append(Var(name))
        return builders, atoms

    def _gen(self, key: str, depth: int, rnd: random.Random) -> Optional[Term]:
        """Sample a well-typed term of base type ``key`` (or None if impossible)."""
        if key == base_key(t_int):
            return Literal(rnd.randrange(self.int_lo, self.int_hi), t_int)
        atoms = self._atoms.get(key, [])
        builders = self._builders.get(key, [])
        # Near the depth limit, prefer atoms and non-recursive builders so that
        # generation always terminates.
        nonrec = [c for c in builders if not any(c.is_recursive_in(k) for k in c.arg_keys)]
        if depth <= 0 or not builders:
            if atoms:
                return rnd.choice(atoms)
            if nonrec:
                return self._apply(rnd.choice(nonrec), depth, rnd)
            if builders:
                return self._apply(rnd.choice(builders), depth, rnd)
            return None
        # Bias toward building structure, occasionally bottoming out at an atom.
        if atoms and rnd.random() >= 0.85:
            return rnd.choice(atoms)
        return self._apply(rnd.choice(builders), depth, rnd)

    def _apply(self, comp: Component, depth: int, rnd: random.Random) -> Optional[Term]:
        term: Term = Var(comp.name)
        for ak in comp.arg_keys:
            arg = self._gen(ak, depth - 1, rnd)
            if arg is None:
                return None
            term = Application(term, arg)
        return term

    # -- term decomposition / mutation ---------------------------------------

    def _positions(self, term: Term) -> list[Term]:
        """Every sub-term that is a candidate mutation site."""
        out: list[Term] = [term]
        head, args = _decompose(term)
        for a in args:
            out.extend(self._positions(a))
        return out

    def _term_key(self, term: Term) -> str:
        if isinstance(term, Literal):
            return base_key(term.type)
        head, _ = _decompose(term)
        if isinstance(head, Var):
            comp = self._by_name.get(head.name)
            if comp is not None:
                return comp.ret_key
            for k, vs in self._atoms.items():
                if any(v.name == head.name for v in vs):
                    return k
        return "?"

    def _mutate(self, term: Term, rnd: random.Random) -> Term:
        positions = self._positions(term)
        target = rnd.choice(positions)
        if isinstance(target, Literal) and base_key(target.type) == base_key(t_int):
            step = rnd.choice([-3, -2, -1, 1, 2, 3])
            replacement: Term = Literal(int(target.value) + step, t_int)  # type: ignore[call-overload]
        else:
            key = self._term_key(target)
            new = self._gen(key, self.max_arg_depth, rnd)
            replacement = new if new is not None else target
        return _replace(term, target, replacement)

    # -- scoring --------------------------------------------------------------

    def _make_score(
        self,
        evaluate: Callable[[Term], list[float]],
        validate: Callable[[Term], bool],
        minimize_flags: list[bool],
    ) -> Callable[[Term], float]:
        cache: dict[str, float] = {}

        def score(term: Term) -> float:
            k = str(term)
            if k in cache:
                return cache[k]
            if not minimize_flags:
                # No metric objective (a pure refinement/validation hole): the
                # distance is binary -- a well-typed term is a solution.
                v = 0.0 if _safe(validate, term) else INF
                cache[k] = v
                return v
            try:
                comps = evaluate(term)
            except (InvalidIndividualException, SynthesisError):
                cache[k] = INF
                return INF
            except Exception:
                cache[k] = INF
                return INF
            if not comps:
                v = 0.0 if _safe(validate, term) else INF
                cache[k] = v
                return v
            flags = minimize_flags or [True] * len(comps)
            s = sum(c if m else -c for c, m in zip(comps, flags))
            cache[k] = s
            return s

        return score

    # -- entry point ----------------------------------------------------------

    def synthesize(
        self,
        ctx: TypingContext,
        type: Type,
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        fun_name: Name,
        metadata: Metadata,
        budget: float = 60,
        ui: SynthesisUI = SynthesisUI(),
    ) -> Term:
        rnd = random.Random(self.seed)
        start = time.time()
        ui.register(None, None, 0, True)

        goals = _goals_for(metadata, fun_name)
        minimize_flags = [g.minimize for g in goals for _ in range(g.length)]

        self._builders, self._atoms = self._collect(ctx)
        self._by_name: dict[Name, Component] = {c.name: c for cs in self._builders.values() for c in cs}
        goal_key = base_key(type)

        score = self._make_score(evaluate, validate, minimize_flags)

        best_term: Optional[Term] = None
        best_score = INF

        def consider(term: Optional[Term]) -> float:
            nonlocal best_term, best_score
            if term is None:
                return INF
            s = score(term)
            if s < best_score:
                best_score = s
                best_term = term
                ui.register(term, [s], time.time() - start, True)
            return s

        def out_of_time() -> bool:
            return (time.time() - start) >= budget

        # 1+2. Construct an approximate version space and cluster by metric.
        # Sample a spread of sizes, heavily weighting shallow candidates: a
        # single large primitive already overlaps the goal and so gives the
        # repair phase a non-flat metric to climb, whereas deep random terms are
        # almost always disjoint from the goal (distance 1).
        clusters: dict[float, tuple[Term, float]] = {}
        tries = 0
        construct_deadline = start + budget * self.construct_fraction
        while len(clusters) < self.pool and time.time() < construct_deadline and tries < self.pool * 8:
            tries += 1
            depth = rnd.randint(0, self.max_arg_depth + 1)
            term = self._gen(goal_key, depth, rnd)
            if term is None:
                continue
            s = consider(term)
            if s == INF:
                continue
            bucket = round(s, 3)
            if bucket not in clusters or s < clusters[bucket][1]:
                clusters[bucket] = (term, s)
            if best_score <= 0.0:
                break

        if best_term is None:
            raise SynthesisNotSuccessful("symetric: could not build any valid candidate")

        # 3+4. Extract closest representatives and repair each via local search.
        seeds = [t for t, _ in sorted(clusters.values(), key=lambda c: c[1])]
        for seed in seeds:
            if out_of_time() or best_score <= 0.0:
                break
            cur, cur_s = seed, score(seed)
            stale = 0
            while not out_of_time() and stale < self.patience and best_score > 0.0:
                cand = self._mutate(cur, rnd)
                s = consider(cand)
                if s < cur_s:
                    cur, cur_s, stale = cand, s, 0
                else:
                    stale += 1

        if best_term is not None and best_score <= 0.0 and _safe(validate, best_term):
            ui.register(best_term, [best_score], time.time() - start, True)
            return best_term
        if best_term is not None and _safe(validate, best_term):
            logger.log("SYNTHESIZER", f"symetric: returning best-effort candidate, distance={best_score}")
            return best_term
        raise SynthesisNotSuccessful(f"symetric: no validated candidate within budget={budget}s")


# -- free helpers ------------------------------------------------------------


def _decompose(term: Term) -> tuple[Term, list[Term]]:
    """Unwind a left-nested application into its head and argument list."""
    args: list[Term] = []
    cur = term
    while isinstance(cur, Application):
        args.append(cur.arg)
        cur = cur.fun
    args.reverse()
    return cur, args


def _rebuild(head: Term, args: list[Term]) -> Term:
    term = head
    for a in args:
        term = Application(term, a)
    return term


def _replace(term: Term, target: Term, replacement: Term) -> Term:
    """Return ``term`` with the first occurrence of ``target`` (by identity)
    replaced by ``replacement``."""
    if term is target:
        return replacement
    head, args = _decompose(term)
    new_args = [_replace(a, target, replacement) for a in args]
    return _rebuild(head, new_args)


def _safe(validate: Callable[[Term], bool], term: Term) -> bool:
    try:
        return validate(term)
    except Exception:
        return False


def _goals_for(metadata: Metadata, fun_name: Name):
    """Read the minimize/maximize goals for this hole, robust to Name identity."""
    entry = metadata.get(fun_name, {})
    goals = entry.get("goals") if isinstance(entry, dict) else None
    if goals:
        return goals
    for _, v in metadata.items():
        if isinstance(v, dict) and v.get("goals"):
            return v["goals"]
    return []
