"""SyMetric: metric program synthesis, as an aeon ``Synthesizer`` backend.

Implements the approach of Feser, Dillig & Solar-Lezama, "Metric Program
Synthesis for Inverse CSG" (arXiv:2206.06164). Where the other backends use
observational *equivalence*, metric synthesis is guided by a distance *metric*
on outputs: programs whose outputs are close to the goal are good, and the
search drives that distance to zero.

The aeon synthesis interface exposes what we need: ``evaluate(term) ->
list[float]`` is the distance of a candidate (e.g. the inverse-CSG Jaccard
distance), ``output_value(term)`` is the candidate's raw output (its "scene"),
and ``validate(term)`` checks well-typedness. The pipeline:

1. **Construct** an approximate version space by a metric-guided beam-search
   *bottom-up enumeration*: round by round, apply every in-scope component
   (inductive constructor / library function) to the bank built so far,
   drawing numeric arguments from a coarse grid.
2. **Cluster** by keeping, at each type, the ``beam`` closest-to-goal
   representatives and de-duplicating by output value (observational
   equivalence) -- the compression that keeps the version space small.
3. **Extract** the representatives closest to the goal.
4. **Repair** them by *tabu search over structured rewrites* -- increment or
   decrement a numeric constant, swap an operator for one of the same
   signature (e.g. union<->diff), graft a near-by sub-term from the bank, or
   regenerate a sub-term -- accepting non-improving moves (with a tabu list)
   to cross the flat plateaus of the distance metric, until it reaches 0 (an
   exact reconstruction, then validated) or the budget ends.

It is, deliberately, *only* a metric synthesiser: it clusters candidates and
steers repair by the distance between their **outputs**, so it applies only when
(a) the hole carries a ``@minimize``/``@maximize`` objective and (b) candidate
outputs live in a space a distance can be computed on -- a number, or a
numeric/boolean vector such as a rasterised scene. On any other hole (no
objective, or an opaque/AST-valued output like the inductive CSG encoding) it
fails immediately with an explanation rather than pretending; use another
backend there.

It clusters by ``output_value`` -- the candidate's output. When the program
denotes its observable directly (a number, or a numeric vector) that is already
the right feature. When it denotes an AST whose scene is derived elsewhere (the
inverse-CSG ``Csg`` term), a ``@cluster(f shape)`` decorator names the
featuriser ``f`` (e.g. ``scene``, which rasterises a candidate to its 0/1
bitmap); ``output_value`` then yields ``f(candidate)`` and clustering is by the
genuine scene distance. Without such a feature, the AST is not a metric space
and the hole is rejected as unsuitable.

Caveat vs. the paper: the authors cluster by *mutual* scene similarity within
epsilon (a goal-independent version space); this backend's beam is also
goal-directed, a weaker compression -- but with a featuriser the distance it
clusters by is the same scene distance.

Selected with ``--synthesizer symetric``.
"""

from __future__ import annotations

import random
import time
from collections import deque
from dataclasses import dataclass
from typing import Any, Callable, Optional

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
    # Needs each candidate's output (it clusters by it), so the evaluation pool
    # computes the (distance, output) pair in one round-trip.
    uses_output_value = True

    def __init__(
        self,
        seed: int = 0,
        int_lo: int = 0,
        int_hi: int = 16,
        beam: int = 12,
        grid_size: int = 5,
        rounds: int = 3,
        combo_cap: int = 40,
        patience: int = 240,
        tabu_size: int = 64,
        max_arg_depth: int = 2,
        construct_fraction: float = 0.3,
        epsilon: float = 0.0,
    ):
        self.seed = seed
        self.int_lo = int_lo
        self.int_hi = int_hi
        self.beam = beam
        self.grid_size = grid_size
        self.rounds = rounds
        self.combo_cap = combo_cap
        self.patience = patience
        self.tabu_size = tabu_size
        self.max_arg_depth = max_arg_depth
        self.construct_fraction = construct_fraction
        self.epsilon = epsilon

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

    # -- bottom-up enumeration (the approximate version space) ----------------

    def _int_grid(self) -> list[int]:
        """A coarse, evenly-spaced grid of integer constants. Enumerating the
        full range for every numeric argument explodes combinatorially; the grid
        covers the space, and repair tunes constants off it."""
        lo, hi = self.int_lo, self.int_hi
        n = max(1, min(self.grid_size, hi - lo))
        if n == 1:
            return [lo]
        step = (hi - 1 - lo) / (n - 1)
        return sorted({lo + round(i * step) for i in range(n)})

    @staticmethod
    def _vectorize(value: object) -> Optional[tuple[float, ...]]:
        """Flatten a candidate's *output* into a numeric feature vector, on which
        a distance can be computed -- e.g. a rasterised scene (a list of
        booleans) becomes a 0/1 vector. Returns ``None`` for outputs that are not
        a number or a (possibly nested, homogeneous) collection of numbers, such
        as opaque objects, strings, or tagged ASTs: those are *not* a space the
        distance metric can operate on, so the metric strategy does not apply."""
        feats: list[float] = []

        def flat(v: object) -> bool:
            if isinstance(v, bool):
                feats.append(1.0 if v else 0.0)
                return True
            if isinstance(v, (int, float)):
                feats.append(float(v))
                return True
            if isinstance(v, (list, tuple, set, frozenset)):
                return all(flat(x) for x in v)
            return False

        return tuple(feats) if flat(value) and feats else None

    @staticmethod
    def _odist(a: Optional[tuple[float, ...]], b: Optional[tuple[float, ...]]) -> float:
        """Mean absolute difference between two output feature vectors -- the
        synthesiser's *own*, goal-independent distance between two candidates'
        outputs (cf. the paper's delta on scenes)."""
        if a is None or b is None or len(a) != len(b) or not a:
            return INF
        return sum(abs(x - y) for x, y in zip(a, b)) / len(a)

    def _require_suitable(
        self,
        goal_type: Type,
        minimize_flags: list[bool],
        output_value: Optional[Callable[[Term], object]],
        rnd: random.Random,
    ) -> None:
        """Raise ``SynthesisNotSuccessful`` unless metric synthesis applies: the
        hole must carry a numeric objective, and candidate outputs must be a
        space a distance can be computed on (numbers, or numeric/boolean
        vectors). Otherwise this strategy cannot help, and we say so."""
        if not minimize_flags:
            raise SynthesisNotSuccessful(
                "symetric is a metric synthesiser: this hole has no @minimize/@maximize "
                "objective to cluster and steer candidates by. Not suitable -- use "
                "another backend (e.g. enumerative, gp, tdsyn)."
            )
        if output_value is None:
            return  # cannot inspect outputs (e.g. a direct call); proceed best-effort
        goal_key = base_key(goal_type)
        saw_output = False
        for _ in range(8):
            term = self._gen(goal_key, self.max_arg_depth, rnd)
            if term is None:
                continue
            try:
                o = output_value(term)
            except Exception:
                continue
            if o is None:
                continue
            saw_output = True
            if self._vectorize(o) is not None:
                return  # a candidate output is a numeric vector: the metric applies
        if saw_output:
            raise SynthesisNotSuccessful(
                "symetric needs candidate outputs to be numbers or numeric/boolean "
                "vectors (e.g. a rasterised scene) so it can measure the distance "
                "between two candidates; this hole's candidates output a value with no "
                "such metric (e.g. an inductive/AST value, as in the CSG encoding). "
                "Not suitable -- expose the output as a feature vector, or use another "
                "backend."
            )

    def _combos(
        self, comp: Component, bank: dict[str, list[Term]], ints: list[Term], cap: int, rnd: random.Random
    ) -> list[Term]:
        """Applications of ``comp`` drawing each argument from the current bank
        (for structured types) or the integer grid (for numeric arguments).
        Enumerates the full product when small, otherwise samples ``cap``."""
        int_key = base_key(t_int)
        pools: list[list[Term]] = []
        for ak in comp.arg_keys:
            pool = ints if ak == int_key else bank.get(ak, [])
            if not pool:
                return []
            pools.append(pool)
        total = 1
        for p in pools:
            total *= len(p)
        out: list[Term] = []
        if total <= cap:
            import itertools

            for choice in itertools.product(*pools):
                term: Term = Var(comp.name)
                for a in choice:
                    term = Application(term, a)
                out.append(term)
        else:
            for _ in range(self.combo_cap):
                term = Var(comp.name)
                for p in pools:
                    term = Application(term, rnd.choice(p))
                out.append(term)
        return out

    def _bottom_up(
        self,
        goal_key: str,
        has_metric: bool,
        consider: Callable[[Optional[Term]], float],
        output_value: Optional[Callable[[Term], object]],
        rnd: random.Random,
        deadline: float,
    ) -> dict[str, list[Term]]:
        """Grow a bank of candidate terms bottom-up, one round per program size,
        keeping at each type the ``beam`` closest-to-goal representatives and
        de-duplicating by output (observational equivalence).

        With a distance metric to guide repair, numeric arguments are drawn from
        a coarse grid (repair tunes them off it). Without one -- a binary
        refinement/validation goal, where there is no gradient -- they are drawn
        from the full range so the exact constants can actually appear."""
        int_key = base_key(t_int)
        grid = self._int_grid() if has_metric else list(range(self.int_lo, self.int_hi))
        ints: list[Term] = [Literal(v, t_int) for v in grid]
        bank: dict[str, list[Term]] = {}
        # Each kept entry is (distance-to-goal, term, output-feature-vector).
        ranked: dict[str, list[tuple[float, Term, Optional[tuple[float, ...]]]]] = {}

        def out_vec(t: Term) -> Optional[tuple[float, ...]]:
            if output_value is None:
                return None
            try:
                return self._vectorize(output_value(t))
            except Exception:
                return None

        def absorb(key: str, terms: list[Term]) -> None:
            scored: list[tuple[float, Term]] = []
            for t in terms:
                if time.time() >= deadline:
                    break
                d = consider(t)
                if d != INF:
                    scored.append((d, t))
            scored.sort(key=lambda x: x[0])
            reps = ranked.get(key, [])
            # Cluster the most promising candidates by *output* similarity: a
            # candidate within epsilon of an existing representative's output is
            # the same "scene", so keep only the one closest to the goal. This is
            # the goal-independent clustering -- distances are between candidates'
            # outputs, not to the goal.
            for d, t in scored[: max(self.beam * 2, 16)]:
                vec = out_vec(t)
                dup = next((i for i, (_, _, rv) in enumerate(reps) if self._odist(vec, rv) <= self.epsilon), None)
                if dup is not None:
                    if d < reps[dup][0]:
                        reps[dup] = (d, t, vec)
                else:
                    reps.append((d, t, vec))
            reps.sort(key=lambda x: x[0])
            ranked[key] = reps[: self.beam]
            bank[key] = [t for _, t, _ in ranked[key]]

        # Round 0: nullary material -- the in-scope atoms, plus, when the goal is
        # itself a number, the whole integer range as candidate answers (a single
        # constant has no combinatorial cost, so we needn't restrict it to the
        # coarse grid the multi-argument builders use).
        for key, vs in self._atoms.items():
            absorb(key, list(vs))
        if goal_key == int_key:
            absorb(int_key, [Literal(v, t_int) for v in range(self.int_lo, self.int_hi)])

        # Validation goals are checked in-process (cheap), so we can enumerate
        # combinations fully; metric goals pay a per-candidate evaluation and
        # stay capped.
        cap = self.combo_cap if has_metric else max(self.combo_cap, 4096)
        for _round in range(self.rounds):
            if time.time() >= deadline:
                break
            for key, comps in self._builders.items():
                for comp in comps:
                    if time.time() >= deadline:
                        break
                    absorb(comp.ret_key, self._combos(comp, bank, ints, cap, rnd))
        return bank

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

    def _neighbors(self, term: Term, bank: dict[str, list[Term]], rnd: random.Random) -> list[Term]:
        """Structured rewrites of ``term`` (the paper's repair moves):
        increment/decrement a numeric constant, swap an operator for one of the
        same signature (e.g. union<->diff), graft a near-by sub-term from the
        bank, or regenerate a sub-term."""
        out: list[Term] = []
        positions = self._positions(term)

        # 1. +/-1 on numeric constants (the paper's increment/decrement).
        int_positions = [p for p in positions if isinstance(p, Literal) and base_key(p.type) == base_key(t_int)]
        rnd.shuffle(int_positions)
        for lit in int_positions[:6]:
            for step in (-1, 1):
                out.append(_replace(term, lit, Literal(int(lit.value) + step, t_int)))  # type: ignore[call-overload]

        # 2. Operator swap: a constructor head -> another with the same signature.
        for sub in positions:
            head, args = _decompose(sub)
            if isinstance(head, Var) and head.name in self._by_name:
                alts = [n for n in self._sig_alts.get(self._by_name[head.name].arg_keys, []) if n != head.name]
                if alts:
                    out.append(_replace(term, sub, _rebuild(Var(rnd.choice(alts)), args)))
                break

        # 3. Graft a same-type representative from the bank.
        graftable = [p for p in positions if bank.get(self._term_key(p))]
        if graftable:
            g_pos = rnd.choice(graftable)
            out.append(_replace(term, g_pos, rnd.choice(bank[self._term_key(g_pos)])))

        # 4. Regenerate a random sub-term.
        if positions:
            r_pos = rnd.choice(positions)
            gen = self._gen(self._term_key(r_pos), self.max_arg_depth, rnd)
            if gen is not None:
                out.append(_replace(term, r_pos, gen))

        base = str(term)
        seen: set[str] = set()
        uniq: list[Term] = []
        for t in out:
            st = str(t)
            if st != base and st not in seen:
                seen.add(st)
                uniq.append(t)
        return uniq

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
        output_value: Callable[[Term], object] | None = None,
    ) -> Term:
        rnd = random.Random(self.seed)
        start = time.time()
        ui.register(None, None, 0, True)

        goals = _goals_for(metadata, fun_name)
        minimize_flags = [g.minimize for g in goals for _ in range(g.length)]

        self._builders, self._atoms = self._collect(ctx)
        self._by_name: dict[Name, Component] = {c.name: c for cs in self._builders.values() for c in cs}
        # Components grouped by argument signature, for operator-swap rewrites.
        self._sig_alts: dict[tuple[str, ...], list[Name]] = {}
        for cs in self._builders.values():
            for c in cs:
                self._sig_alts.setdefault(c.arg_keys, []).append(c.name)
        goal_key = base_key(type)

        # SyMetric is a *metric* synthesiser: it clusters candidates and steers
        # repair by the distance between their outputs. Fail fast, with a clear
        # message, on holes where that strategy does not apply.
        self._require_suitable(type, minimize_flags, output_value, rnd)

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

        # 1+2. Construct + cluster: a metric-guided beam-search bottom-up
        # enumeration. Each round grows programs one operator deeper, keeping at
        # each type the `beam` closest-to-goal representatives and de-duplicating
        # by output (observational equivalence), so the version space stays
        # small while systematically covering structures.
        construct_deadline = start + budget * self.construct_fraction
        bank = self._bottom_up(goal_key, bool(minimize_flags), consider, output_value, rnd, construct_deadline)

        # A few random terms as a safety net if the bank missed the goal type.
        while goal_key not in bank and not out_of_time() and time.time() < construct_deadline:
            consider(self._gen(goal_key, rnd.randint(0, self.max_arg_depth + 1), rnd))
            break

        if best_term is None:
            raise SynthesisNotSuccessful("symetric: could not build any valid candidate")

        # 3+4. Extract the closest representatives and repair each by tabu search
        # over structured rewrites. Tabu (and accepting non-improving moves) lets
        # repair cross the flat plateaus of the distance metric.
        seeds = list(bank.get(goal_key, []))
        if best_term is not None and best_term not in seeds:
            seeds.insert(0, best_term)
        # Repair every representative in parallel, one tabu step at a time
        # (round-robin), so a structurally-different seed -- e.g. a *union* of two
        # primitives -- keeps getting search effort instead of all of it being
        # spent on the single closest seed, which is often a strong local optimum.
        searches: list[dict[str, Any]] = [
            {"cur": s, "cur_s": score(s), "tabu": deque(maxlen=self.tabu_size), "stale": 0} for s in seeds[: self.beam]
        ]
        for st in searches:
            st["tabu"].append(str(st["cur"]))
        while searches and not out_of_time() and best_score > 0.0:
            for st in list(searches):
                if out_of_time() or best_score <= 0.0:
                    break
                if st["stale"] >= self.patience:
                    searches.remove(st)
                    continue
                neighbors = self._neighbors(st["cur"], bank, rnd)
                rnd.shuffle(neighbors)
                pick: Optional[Term] = None
                pick_s = INF
                for n in neighbors[:8]:  # a sampled neighbourhood keeps steps cheap
                    if out_of_time():
                        break
                    if str(n) in st["tabu"]:
                        continue
                    s = consider(n)
                    if s < pick_s:
                        pick, pick_s = n, s
                if pick is None:
                    searches.remove(st)
                    continue
                st["stale"] = 0 if pick_s < st["cur_s"] else st["stale"] + 1
                st["cur"], st["cur_s"] = pick, pick_s
                st["tabu"].append(str(pick))

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
