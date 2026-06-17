"""FTA: spec-guided program synthesis via Finite Tree Automata.

Implements the core construction of Wang, Dillig & Singh, "Synthesis of Data
Completion Scripts using Finite Tree Automata" (OOPSLA 2017). Bottom-up over the
DSL's components, it builds a finite tree automaton whose

* **states** ``q`` are observational-equivalence classes of sub-programs -- in
  the paper, the concrete value a sub-program produces on the input example;
  here, a candidate's concrete output as exposed by aeon's ``output_value``,
* **alphabet** are the in-scope components (inductive constructors / library
  functions), each a ranked transition ``f(q1, ..., qk) -> q``,
* **accepting states** are those consistent with the specification.

The defining feature of the FTA is *compression by observational equivalence*:
many syntactically distinct programs collapse into one state per distinct
output, so the automaton compactly represents the whole version space of
spec-consistent programs, and a single (minimal) program is extracted from it.
The pay-off is that the spec is checked **once per state**, not once per program.

How the paper maps onto aeon. The paper accepts a program iff it reproduces a
concrete output *example*; aeon specifies a hole by a *refinement type*, so this
backend's acceptance oracle is ``validate`` (the liquid typechecker), and it
materialises the automaton's value-states at the hole's type, where aeon exposes
a candidate's concrete output via ``output_value``. Because output is observable
only at the hole type, observational-equivalence merging -- and the resulting
once-per-class validation -- happens there; structured arguments are drawn from
the bottom-up bank, exactly as in FTA construction, but are not separately
observed. Requiring no objective/metric, this is the backend of choice for the
refinement holes that the metric synthesiser (``symetric``) rejects.

The repo's ``lta`` backend (Liquid Tree Automata, arXiv:2605.13456) is the
refinement-typed descendant of this line of work; abstraction-refinement FTAs
(``afta``, Wang/Dillig/Singh POPL'18) and constraint-annotated tree automata
(``cata``) sit between this concrete FTA and LTA, and are tracked as follow-ups.

Selected with ``--synthesizer fta``.
"""

from __future__ import annotations

import itertools
import random
import time
from typing import Any, Callable, Optional

from loguru import logger

from aeon.backend.evaluator import EvaluationContext
from aeon.backend.evaluator import eval as aeon_eval
from aeon.core.substitutions import substitution
from dataclasses import dataclass, field

from aeon.core.terms import Application, Literal, Term, TypeApplication, Var
from aeon.core.types import (
    AbstractionType,
    Type,
    TypeConstructor,
    TypePolymorphism,
    t_float,
    t_int,
)
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer, SynthesisNotSuccessful
from aeon.synthesis.modules.symetric.synthesizer import (
    _decompose,
    _peel,
    base_key,
)
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext, VariableBinder
from aeon.utils.name import Name

# An automaton state: ("val", frozen-output) for an observed value, or
# ("term", str) for a sub-program whose output aeon cannot observe (kept
# distinct so unobservable candidates are never wrongly merged).
StateKey = tuple[str, Any]


@dataclass(frozen=True)
class _MonoComponent:
    """A builder for candidate terms: a function/constructor, plus the concrete
    type arguments to instantiate it at (``type_apps`` empty for monomorphic
    bindings; non-empty when a polymorphic operator like ``+ : ∀a. a -> a -> a``
    has been monomorphized, so it is applied as ``(+)[Int] q1 q2``)."""

    name: Name
    arg_keys: tuple[str, ...]
    ret_key: str
    type_apps: tuple[Type, ...] = field(default_factory=tuple)


class FTASynthesizer(Synthesizer):
    """Component-based synthesis by building a finite tree automaton bottom-up
    and extracting the smallest spec-consistent program from it."""

    # Evaluation context, stashed in ``computations`` (called before ``synthesize``)
    # so example-driven runs can evaluate candidates on concrete @example/@csv inputs.
    _ectx: Optional[EvaluationContext] = None

    def computations(self, primitives: Any) -> dict[str, Any]:
        # The automaton keys states by each candidate's concrete *output*; the
        # pool computes it (a ``@cluster`` featuriser, else the candidate value).
        # Stash the evaluation context so example-driven runs can observe a
        # candidate's output on concrete @example/@csv inputs (paper-faithful FTA).
        self._ectx = primitives.ectx
        return {"output": primitives.feature}

    def __init__(
        self,
        seed: int = 0,
        int_lo: int = -8,
        int_hi: int = 33,
        rounds: int = 3,
        combo_cap: int = 4096,
        max_bank: int = 512,
    ):
        self.seed = seed
        self.int_lo = int_lo
        self.int_hi = int_hi
        self.rounds = rounds
        self.combo_cap = combo_cap
        self.max_bank = max_bank

    # -- components -----------------------------------------------------------

    def _collect(
        self, ctx: TypingContext, inst_types: set[TypeConstructor]
    ) -> tuple[dict[str, list[_MonoComponent]], dict[str, list[Var]]]:
        """Index the in-scope bindings as builders (functions/constructors, the
        automaton's ranked alphabet) and atoms (nullary leaves). Polymorphic
        operators (``+``/``*``/… : ``∀a. a -> a -> a``) are monomorphized at
        ``inst_types`` so the search can build functions of the input over them."""
        from aeon.synthesis.grammar.grammar_generation import monomorphize_poly_type

        builders: dict[str, list[_MonoComponent]] = {}
        atoms: dict[str, list[Var]] = {}

        def consider(name: Name, arg_types: list[Type], ret: Type, tapps: tuple[Type, ...]) -> None:
            if any(isinstance(a, (AbstractionType, TypePolymorphism)) for a in arg_types):
                return  # no higher-order arguments
            if isinstance(ret, (AbstractionType, TypePolymorphism)):
                return
            ret_key = base_key(ret)
            if arg_types:
                comp = _MonoComponent(name, tuple(base_key(a) for a in arg_types), ret_key, tapps)
                builders.setdefault(ret_key, []).append(comp)
            elif not tapps:
                atoms.setdefault(ret_key, []).append(Var(name))

        for name, ty in ctx.concrete_vars():
            if isinstance(ty, TypePolymorphism):
                for body, type_apps in monomorphize_poly_type(ty, inst_types):
                    arg_types, ret = _peel(body)
                    consider(name, arg_types, ret, tuple(type_apps))
            else:
                arg_types, ret = _peel(ty)
                consider(name, arg_types, ret, ())
        return builders, atoms

    def _head(self, comp: _MonoComponent) -> Term:
        term: Term = Var(comp.name)
        for ta in comp.type_apps:
            term = TypeApplication(term, ta)
        return term

    def _combos(
        self, comp: _MonoComponent, bank: dict[str, list[Term]], deadline: float, rnd: random.Random
    ) -> list[Term]:
        """Transitions ``comp(q1, ..., qk) -> q``: applications of ``comp`` whose
        arguments are drawn from the current bank (per argument type). Enumerates
        the full product when small, else samples ``combo_cap`` of it."""
        pools: list[list[Term]] = []
        for ak in comp.arg_keys:
            pool = bank.get(ak, [])
            if not pool:
                return []
            pools.append(pool)
        total = 1
        for p in pools:
            total *= len(p)
        out: list[Term] = []
        if total <= self.combo_cap:
            for choice in itertools.product(*pools):
                if time.time() >= deadline:
                    break
                term = self._head(comp)
                for a in choice:
                    term = Application(term, a)
                out.append(term)
        else:
            for _ in range(self.combo_cap):
                term = self._head(comp)
                for p in pools:
                    term = Application(term, rnd.choice(p))
                out.append(term)
        return out

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
        start = time.time()
        deadline = start + budget
        rnd = random.Random(self.seed)
        ui.register(None, None, 0, True)

        # Instantiate polymorphic operators at the numeric base types plus the
        # goal type, so the bottom-up search can build arithmetic over the input.
        inst_types: set[TypeConstructor] = {t_int, t_float}
        _gret = _peel(type)[1]
        if isinstance(_gret, TypeConstructor):
            inst_types.add(_gret)

        builders, atoms = self._collect(ctx, inst_types)
        goal_key = base_key(type)
        int_key = base_key(t_int)
        float_key = base_key(t_float)

        # Example-driven (paper-faithful) mode: when @example/@csv give concrete
        # input/output rows for this function, key each state by the candidate's
        # output *vector* across those inputs (observational equivalence over the
        # examples, as in Wang/Dillig/Singh) and accept the state whose vector
        # matches the expected outputs. This is what lets the FTA synthesize a
        # function *of its input* (e.g. x + 1) rather than only constants.
        arg_binders = _arg_binders(ctx, fun_name)
        rows = _example_rows(metadata, fun_name)
        expecteds = tuple(r[-1] for r in rows)
        example_mode = (
            bool(rows)
            and self._ectx is not None
            and bool(arg_binders)
            and len(arg_binders) == len(rows[0]) - 1
            and all(_example_literal(0.0, ty) is not None for _n, ty in arg_binders)
        )

        # The automaton, materialised at the goal type: each observational state
        # keeps its smallest representative; the spec is checked once per state.
        rep: dict[StateKey, Term] = {}
        validated: dict[StateKey, bool] = {}
        transitions = 0
        best: Optional[Term] = None

        def obs_default(term: Term) -> StateKey:
            """The observational state of a goal-typed term -- its concrete
            output. Falls back to a literal's syntactic value, and otherwise
            keeps the term distinct (no unsound merge)."""
            if output_value is not None:
                try:
                    v = output_value(term)
                except Exception:
                    v = None
                if v is not None:
                    try:
                        return ("val", _freeze(v))
                    except TypeError:
                        return ("val", repr(v))
            if isinstance(term, Literal):
                return ("val", term.value)
            return ("term", str(term))

        def obs_examples(term: Term) -> StateKey:
            """The candidate's output vector over the example inputs: bind the
            function's parameters to each row's inputs and evaluate. A candidate
            that cannot be evaluated stays its own (unmerged) state."""
            outs: list[Any] = []
            for r in rows:
                sub = term
                for (nm, ty), v in zip(arg_binders, r[:-1]):
                    lit = _example_literal(v, ty)
                    assert lit is not None  # guaranteed by example_mode
                    sub = substitution(sub, lit, nm)
                try:
                    outs.append(_freeze(aeon_eval(sub, self._ectx)))
                except Exception:
                    return ("term", str(term))
            return ("vec", tuple(outs))

        def matches_examples(st: StateKey) -> bool:
            if st[0] != "vec":
                return False
            out = st[1]
            return len(out) == len(expecteds) and all(_close(o, e) for o, e in zip(out, expecteds))

        obs = obs_examples if example_mode else obs_default

        def insert_goal(term: Term) -> None:
            """Add a goal-typed term to the automaton: merge by observational
            equivalence (keep the smallest representative) and validate the
            state's representative once."""
            nonlocal best
            st = obs(term)
            cur = rep.get(st)
            if cur is None or _term_size(term) < _term_size(cur):
                rep[st] = term
            if st not in validated:
                ok = _safe(validate, rep[st])
                if example_mode:
                    # The examples are part of the spec: a candidate must both
                    # type-check (refinement, if any) and reproduce every example.
                    ok = ok and matches_examples(st)
                validated[st] = ok
            if validated[st]:
                cand = rep[st]
                if best is None or _term_size(cand) < _term_size(best):
                    best = cand
                    ui.register(best, [0.0], time.time() - start, True)

        bank: dict[str, list[Term]] = {}
        seen: dict[str, set[str]] = {}

        def add_bank(key: str, terms: list[Term]) -> None:
            b = bank.setdefault(key, [])
            s = seen.setdefault(key, set())
            for t in terms:
                k = str(t)
                if k in s:
                    continue
                s.add(k)
                b.append(t)
                if key == goal_key:
                    insert_goal(t)
            if len(b) > self.max_bank:
                del b[self.max_bank :]

        # Round 0 -- nullary leaves: the in-scope atoms, plus the integer range
        # (available both as candidate answers and as numeric arguments).
        for key, vs in atoms.items():
            add_bank(key, list(vs))
        add_bank(int_key, [Literal(v, t_int) for v in range(self.int_lo, self.int_hi)])
        add_bank(float_key, [Literal(v, t_float) for v in (0.0, 1.0, 2.0, -1.0)])

        # Rounds 1..k -- apply every transition to the bank built so far, growing
        # programs one operator deeper. Stop as soon as an accepting state is
        # found: bottom-up construction reaches the smallest programs first.
        for _round in range(self.rounds):
            if best is not None or time.time() >= deadline:
                break
            snapshot = {k: list(v) for k, v in bank.items()}
            for comps in builders.values():
                for comp in comps:
                    if best is not None or time.time() >= deadline:
                        break
                    new_terms = self._combos(comp, snapshot, deadline, rnd)
                    transitions += len(new_terms)
                    add_bank(comp.ret_key, new_terms)

        states = len(rep)
        if best is not None:
            logger.log(
                "SYNTHESIZER",
                f"fta: solution found; automaton had {states} states / {transitions} transitions "
                f"at the goal type (version space compressed by observational equivalence)",
            )
            ui.register(best, [0.0], time.time() - start, True)
            return best
        raise SynthesisNotSuccessful(
            f"fta: no spec-consistent program of depth < {self.rounds} found within budget={budget}s "
            f"(explored {states} observational states / {transitions} transitions). Try a larger budget, "
            "more rounds, or a backend that abstracts states (afta/lta)."
        )


# -- free helpers ------------------------------------------------------------


def _term_size(term: Term) -> int:
    """Node count of a term -- the size measure minimised during extraction."""
    _head, args = _decompose(term)
    return 1 + sum(_term_size(a) for a in args)


def _freeze(v: object) -> Any:
    """A hashable, order-stable view of a candidate's output, so that equal
    outputs map to the same automaton state regardless of container type."""
    if isinstance(v, (list, tuple)):
        return tuple(_freeze(x) for x in v)
    if isinstance(v, (set, frozenset)):
        return frozenset(_freeze(x) for x in v)
    if isinstance(v, dict):
        return tuple(sorted((k, _freeze(x)) for k, x in v.items()))
    return v


def _safe(validate: Callable[[Term], bool], term: Term) -> bool:
    try:
        return validate(term)
    except Exception:
        return False


def _close(o: object, e: object) -> bool:
    """Numeric equality with a float tolerance; exact for everything else."""
    try:
        return abs(float(o) - float(e)) < 1e-6  # type: ignore[arg-type]
    except (TypeError, ValueError):
        return o == e


def _arg_binders(ctx: TypingContext, fun_name: Name) -> list[tuple[Name, Type]]:
    """The synthesized function's parameters ``(name, type)``, in order -- the
    value binders introduced after the function itself in the hole's context
    (same heuristic the decision-tree backend uses)."""
    found = False
    out: list[tuple[Name, Type]] = []
    for e in ctx.entries:
        if isinstance(e, VariableBinder):
            if e.name.name == fun_name.name:
                found = True
                continue
            if found:
                out.append((e.name, e.type))
    return out


def _example_rows(metadata: Metadata, fun_name: Name) -> list[list[float]]:
    """Concrete input/output rows recorded for ``fun_name`` -- each
    ``[in_1, ..., in_n, expected]``. Populated by ``@example`` (numeric
    assertions) and by ``@csv_data``/``@csv_file`` (one row per data point),
    both under the ``training_data`` metadata key."""
    for key, entry in metadata.items():
        if isinstance(entry, dict) and getattr(key, "name", None) == fun_name.name:
            return [list(r) for r in (entry.get("training_data") or [])]
    return []


def _example_literal(value: float, ty: Type) -> Optional[Term]:
    """A core literal of ``ty`` for a numeric example value, or ``None`` when the
    parameter type is not Int/Float (so example mode does not apply)."""
    key = base_key(ty)
    if key == base_key(t_int):
        return Literal(int(value), t_int)
    if key == base_key(t_float):
        return Literal(float(value), t_float)
    return None
