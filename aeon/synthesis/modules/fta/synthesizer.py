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

from aeon.core.terms import Application, Literal, Term, Var
from aeon.core.types import (
    AbstractionType,
    Type,
    TypePolymorphism,
    t_int,
)
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer, SynthesisNotSuccessful
from aeon.synthesis.modules.symetric.synthesizer import (
    Component,
    _decompose,
    _peel,
    base_key,
)
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name

# An automaton state: ("val", frozen-output) for an observed value, or
# ("term", str) for a sub-program whose output aeon cannot observe (kept
# distinct so unobservable candidates are never wrongly merged).
StateKey = tuple[str, Any]


class FTASynthesizer(Synthesizer):
    """Component-based synthesis by building a finite tree automaton bottom-up
    and extracting the smallest spec-consistent program from it."""

    def computations(self, primitives: Any) -> dict[str, Any]:
        # The automaton keys states by each candidate's concrete *output*; the
        # pool computes it (a ``@cluster`` featuriser, else the candidate value).
        return {"output": primitives.feature}

    def __init__(
        self,
        seed: int = 0,
        int_lo: int = 0,
        int_hi: int = 8,
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

    def _collect(self, ctx: TypingContext) -> tuple[dict[str, list[Component]], dict[str, list[Var]]]:
        """Index the in-scope bindings as builders (functions/constructors, the
        automaton's ranked alphabet) and atoms (nullary leaves)."""
        builders: dict[str, list[Component]] = {}
        atoms: dict[str, list[Var]] = {}
        for name, ty in ctx.concrete_vars():
            if name.name in ("%", "/"):
                # Partial operators: undefined on a zero divisor. The verifier
                # here does not enforce a non-zero-divisor precondition, so a
                # ``x % 0`` term is both well-typed and (via z3's unspecified
                # mod-by-zero) spec-consistent -- a spurious accepting state.
                # Keep them out of the automaton's alphabet.
                continue
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

    def _combos(self, comp: Component, bank: dict[str, list[Term]], deadline: float, rnd: random.Random) -> list[Term]:
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

        builders, atoms = self._collect(ctx)
        goal_key = base_key(type)
        int_key = base_key(t_int)

        # The automaton, materialised at the goal type: each observational state
        # keeps its smallest representative; the spec is checked once per state.
        rep: dict[StateKey, Term] = {}
        validated: dict[StateKey, bool] = {}
        transitions = 0
        best: Optional[Term] = None

        def obs(term: Term) -> StateKey:
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
                validated[st] = _safe(validate, rep[st])
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
