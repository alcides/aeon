"""AFTA: spec-guided synthesis via *Abstraction-Refinement* Finite Tree Automata.

Implements the line of Wang, Dillig & Singh, "Program Synthesis using
Abstraction Refinement" (POPL 2018, arXiv:1710.07740) -- the direct successor of
the concrete FTA backend (``fta``, OOPSLA'17).

Where ``fta`` keys automaton states by a candidate's *concrete* output (one
state per distinct output value), AFTA keys them by an *abstract* value: the
candidate's image under a **predicate abstraction**. The abstract domain is a
set ``P`` of predicates drawn from the hole's refinement; the abstract value of
a sub-program is the truth-vector ``(p(v))_{p in P}`` of those predicates on its
concrete output ``v``. Because many concrete outputs share one truth-vector, the
abstract automaton is far smaller than the concrete one -- the central pay-off
of the paper.

The spec is checked *under the abstraction*: a state is accepting iff its
truth-vector is consistent with the goal refinement. An abstractly-accepting
state need not be concretely accepting, though: a coarse ``P`` lumps satisfying
and non-satisfying values into one state. So AFTA runs a **CEGAR** loop:

1. start from the coarsest abstraction (``P`` empty -- every value collapses to
   one state),
2. build the tree automaton bottom-up and extract the smallest abstractly-
   accepting program,
3. **validate** it with the liquid typechecker (the concrete oracle, exactly as
   in ``fta``); if it holds, return it,
4. otherwise the acceptance was *spurious* -- the abstraction was too coarse.
   **Refine**: harvest the goal conjunct(s) the failed candidate violates, add
   them to ``P``, re-abstract (splitting the offending state), and retry.

The loop converges: each refinement adds a real goal conjunct, so once ``P``
covers all conjuncts the abstraction is precise and no spurious acceptance
remains. Soundness never rests on the abstraction -- the returned program is
always ``validate``-checked -- so the lightweight predicate evaluator used for
abstraction only affects *which* programs are tried and *how* the search prunes,
never *whether* an accepted program is correct.

Relation to the rest of the line. ``fta`` (concrete states) -> ``afta`` (this:
predicate-abstract states + CEGAR) -> ``lta`` (Liquid Tree Automata,
arXiv:2605.13456: entailment-constrained states). Like ``fta``, AFTA needs no
``@minimize``/``@maximize`` objective: a pure refinement hole is enough.

Selected with ``--synthesizer afta``.
"""

from __future__ import annotations

import itertools
import random
import time
from typing import Any, Callable, Optional

from loguru import logger

from aeon.core.liquid import (
    LiquidApp,
    LiquidLiteralBool,
    LiquidLiteralFloat,
    LiquidLiteralInt,
    LiquidLiteralString,
    LiquidTerm,
    LiquidVar,
)
from aeon.core.terms import Application, Literal, Term, Var
from aeon.core.types import (
    AbstractionType,
    RefinedType,
    Type,
    TypePolymorphism,
    t_int,
)
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer, SynthesisNotSuccessful
from aeon.synthesis.modules.fta.synthesizer import _freeze, _safe, _term_size
from aeon.synthesis.modules.symetric.synthesizer import (
    Component,
    _peel,
    base_key,
)
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


class _Unevaluable(Exception):
    """Raised when a predicate cannot be evaluated concretely (e.g. it mentions
    an uninterpreted function or a value of a non-scalar type). Such predicates
    are simply left out of the abstraction -- they never compromise soundness,
    since the concrete oracle (``validate``) is the final word."""


# A predicate's abstract value on one candidate output: True/False, or ``None``
# when it could not be evaluated. The abstract state of a goal-typed term is the
# tuple of these over the active predicate set ``P`` -- the automaton's state key.
Truth = Optional[bool]
Signature = tuple[Any, ...]


class AFTASynthesizer(Synthesizer):
    """Component-based synthesis by building a *predicate-abstract* tree
    automaton bottom-up and refining the abstraction (CEGAR) until the smallest
    abstractly-accepting program is concretely validated."""

    def computations(self, primitives: Any) -> dict[str, Any]:
        # The abstraction is computed from each candidate's concrete *output*;
        # the pool computes it (a ``@cluster`` featuriser, else the value).
        return {"output": primitives.feature}

    def __init__(
        self,
        seed: int = 0,
        int_lo: int = -8,
        int_hi: int = 33,
        rounds: int = 3,
        combo_cap: int = 4096,
        max_bank: int = 512,
        max_refine: int = 16,
    ):
        self.seed = seed
        self.int_lo = int_lo
        self.int_hi = int_hi
        self.rounds = rounds
        self.combo_cap = combo_cap
        self.max_bank = max_bank
        # CEGAR is naturally bounded by the number of goal conjuncts, but this
        # caps it defensively against pathological refinements.
        self.max_refine = max_refine

    # -- components (identical alphabet to the concrete FTA) -------------------

    def _collect(self, ctx: TypingContext) -> tuple[dict[str, list[Component]], dict[str, list[Var]]]:
        """Index the in-scope bindings as builders (the automaton's ranked
        alphabet) and atoms (nullary leaves) -- the same component collection
        the concrete FTA uses."""
        builders: dict[str, list[Component]] = {}
        atoms: dict[str, list[Var]] = {}
        for name, ty in ctx.concrete_vars():
            if isinstance(ty, TypePolymorphism):
                continue
            arg_types, ret = _peel(ty)
            if any(isinstance(a, (AbstractionType, TypePolymorphism)) for a in arg_types):
                continue
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
        arguments are drawn from the current bank (per argument type)."""
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

        # The predicate abstraction's universe: the goal refinement's top-level
        # conjuncts, each a candidate predicate over the refinement variable.
        # Only conjuncts our lightweight evaluator can decide are usable; the
        # rest are dropped (validate still has the final say).
        refvar, all_atoms = _refinement_atoms(type)

        def obs_value(term: Term) -> tuple[bool, Any]:
            """A goal-typed term's concrete output, if observable. Returns
            ``(observed, value)``; ``observed=False`` means the term's value is
            opaque to the abstraction (it must then be validated directly)."""
            if output_value is not None:
                try:
                    v = output_value(term)
                except Exception:
                    v = None
                if v is not None:
                    return True, v
            if isinstance(term, Literal):
                return True, term.value
            return False, None

        def signature(term: Term, value_ok: bool, value: Any, active: list[LiquidTerm]) -> Signature:
            """The automaton state of a goal term under abstraction ``active``:
            the truth-vector of the active predicates on its output. With ``P``
            empty every observable output collapses to one state (``("val",
            ())``) -- the coarsest abstraction the CEGAR loop starts from. Opaque
            outputs (no observable value) get a per-term singleton state so they
            are never merged unsoundly, and are always treated as candidates."""
            if not value_ok:
                return ("opaque", str(term))  # validated individually, never merged
            truths: list[Truth] = []
            for atom in active:
                try:
                    truths.append(_eval_pred(atom, refvar, value))
                except _Unevaluable:
                    truths.append(None)
            return ("val", tuple(truths))

        # -- bottom-up bank, identical to the concrete FTA construction --------
        bank: dict[str, list[Term]] = {}
        seen: dict[str, set[str]] = {}
        goal_terms: list[Term] = []

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
                    goal_terms.append(t)
            if len(b) > self.max_bank:
                del b[self.max_bank :]

        for key, vs in atoms.items():
            add_bank(key, list(vs))
        add_bank(int_key, [Literal(v, t_int) for v in range(self.int_lo, self.int_hi)])

        # Active predicate set P (indices into all_atoms), grown by CEGAR.
        active_idx: list[int] = []
        tried: set[str] = set()  # goal terms already validated-false (skip them)
        refinements = 0
        solve_abstract = 0  # automaton size at the pass that found the solution
        solve_concrete = 0  # concrete observational classes at that same pass

        def active_atoms() -> list[LiquidTerm]:
            return [all_atoms[i] for i in active_idx]

        def cegar_pass() -> Optional[Term]:
            """Build the abstract automaton over the current goal-term bank,
            extract the smallest abstractly-accepting program, validate it, and
            refine the abstraction on a spurious acceptance. Returns a validated
            program, or ``None`` when this depth's bank is exhausted."""
            nonlocal refinements, solve_abstract, solve_concrete
            for _ in range(self.max_refine + 1):
                if time.time() >= deadline:
                    return None
                active = active_atoms()
                # Build the automaton: collapse goal terms into abstract states,
                # keeping each state's smallest representative.
                states: dict[Signature, tuple[Term, bool, Any]] = {}
                concrete: set[Any] = set()
                for t in goal_terms:
                    if str(t) in tried:
                        continue
                    ok, val = obs_value(t)
                    if ok:
                        try:
                            concrete.add(_freeze(val))
                        except TypeError:
                            concrete.add(repr(val))
                    sig = signature(t, ok, val, active)
                    cur = states.get(sig)
                    if cur is None or _term_size(t) < _term_size(cur[0]):
                        states[sig] = (t, ok, val)

                # Abstractly-accepting states: opaque ones (decided by validate)
                # and value-states whose active predicates are all satisfied.
                accepting = [(t, ok, val) for sig, (t, ok, val) in states.items() if _is_accepting(sig)]
                accepting.sort(key=lambda e: _term_size(e[0]))

                refined = False
                for term, ok, val in accepting:
                    if time.time() >= deadline:
                        return None
                    if _safe(validate, term):
                        solve_abstract, solve_concrete = len(states), len(concrete)
                        return term
                    tried.add(str(term))
                    # Spurious acceptance: the abstraction was too coarse. Add
                    # one goal conjunct this candidate violates to the predicate
                    # set (CEGAR refine) and rebuild -- this splits the offending
                    # state. One predicate per round keeps the abstraction as
                    # coarse as possible for as long as possible.
                    if ok:
                        new = _violated_unseen(all_atoms, active_idx, refvar, val)
                        if new:
                            active_idx.append(new[0])
                            refinements += 1
                            refined = True
                            break
                if not refined:
                    # No abstractly-accepting candidate survived and nothing new
                    # to refine on: the abstraction is precise at this depth.
                    return None
            return None

        # -- interleave bottom-up growth with CEGAR refinement ----------------
        # Try to solve at the current depth (refining the abstraction to
        # convergence); only deepen the program bank when that depth is dry.
        solution = cegar_pass()
        for _round in range(self.rounds):
            if solution is not None or time.time() >= deadline:
                break
            snapshot = {k: list(v) for k, v in bank.items()}
            for comps in builders.values():
                for comp in comps:
                    if time.time() >= deadline:
                        break
                    add_bank(comp.ret_key, self._combos(comp, snapshot, deadline, rnd))
            solution = cegar_pass()

        if solution is not None:
            ui.register(solution, [0.0], time.time() - start, True)
            compression = (solve_concrete / solve_abstract) if solve_abstract else 1.0
            logger.log(
                "SYNTHESIZER",
                f"afta: solution found after {refinements} abstraction refinement(s); "
                f"the abstract automaton had {solve_abstract} state(s) vs {solve_concrete} concrete "
                f"observational classes ({compression:.1f}x compression at the goal type).",
            )
            return solution
        raise SynthesisNotSuccessful(
            f"afta: no spec-consistent program of depth < {self.rounds} found within budget={budget}s "
            f"(after {refinements} refinement(s)). Try a larger budget or more rounds."
        )


# -- abstraction helpers -----------------------------------------------------


def _is_accepting(sig: Signature) -> bool:
    """A state is accepting under the abstraction iff it is opaque (deferred to
    ``validate``) or all of its decided active predicates hold. Undecided
    (``None``) predicates are treated optimistically -- an over-approximation
    the CEGAR loop later tightens."""
    if sig and sig[0] == "opaque":
        return True
    if not sig or sig[0] != "val":
        return True
    truths = sig[1]
    return all(t is not False for t in truths)


def _violated_unseen(all_atoms: list[LiquidTerm], active_idx: list[int], refvar: Name, value: Any) -> list[int]:
    """Indices of goal conjuncts not yet in the abstraction that ``value``
    violates -- the predicates CEGAR adds to split a spuriously-accepting
    state."""
    out: list[int] = []
    active = set(active_idx)
    for i, atom in enumerate(all_atoms):
        if i in active:
            continue
        try:
            if not _eval_pred(atom, refvar, value):
                out.append(i)
        except _Unevaluable:
            continue
    return out


def _refinement_atoms(ty: Type) -> tuple[Name, list[LiquidTerm]]:
    """The refinement variable and the top-level conjuncts of a refinement type.
    Non-refined (or unrefined) goal types yield no predicates -- AFTA then runs
    the coarsest abstraction throughout, degrading gracefully to the concrete
    FTA's once-per-output validation."""
    if not isinstance(ty, RefinedType):
        return Name("_", 0), []
    return ty.name, _conjuncts(ty.refinement)


def _conjuncts(t: LiquidTerm) -> list[LiquidTerm]:
    """Flatten a refinement's top-level ``&&`` conjunction into atomic
    predicates."""
    if isinstance(t, LiquidApp) and t.fun.name == "&&" and len(t.args) == 2:
        return _conjuncts(t.args[0]) + _conjuncts(t.args[1])
    if isinstance(t, LiquidLiteralBool) and t.value:
        return []  # trivially-true conjunct carries no information
    return [t]


# A small concrete interpreter for liquid predicates. It is deliberately partial
# -- anything it does not recognise raises ``_Unevaluable`` and is excluded from
# the abstraction. It is used ONLY to shape and prune the search; correctness of
# every returned program is decided by ``validate``, never by this evaluator.
_BINOPS: dict[str, Callable[[Any, Any], Any]] = {
    "==": lambda a, b: a == b,
    "!=": lambda a, b: a != b,
    "<": lambda a, b: a < b,
    "<=": lambda a, b: a <= b,
    ">": lambda a, b: a > b,
    ">=": lambda a, b: a >= b,
    "+": lambda a, b: a + b,
    "-": lambda a, b: a - b,
    "*": lambda a, b: a * b,
    "&&": lambda a, b: bool(a) and bool(b),
    "||": lambda a, b: bool(a) or bool(b),
    "-->": lambda a, b: (not bool(a)) or bool(b),
}


def _eval_pred(atom: LiquidTerm, refvar: Name, value: Any) -> bool:
    """Evaluate a refinement predicate with the refinement variable bound to a
    candidate's concrete output. Raises ``_Unevaluable`` on anything outside the
    supported scalar/boolean/arithmetic fragment -- including operand-type
    mismatches (e.g. an arithmetic atom applied to a non-numeric output)."""
    try:
        return bool(_eval(atom, refvar, value))
    except (TypeError, ValueError, ZeroDivisionError, OverflowError):
        raise _Unevaluable()


def _eval(t: LiquidTerm, refvar: Name, value: Any) -> Any:
    if isinstance(t, LiquidVar):
        if t.name == refvar:
            return value
        raise _Unevaluable()  # free variable other than the refinement var
    if isinstance(t, LiquidLiteralBool):
        return t.value
    if isinstance(t, (LiquidLiteralInt, LiquidLiteralFloat, LiquidLiteralString)):
        return t.value
    if isinstance(t, LiquidApp):
        op = t.fun.name
        if op == "!" and len(t.args) == 1:
            return not bool(_eval(t.args[0], refvar, value))
        if op in ("/", "%") and len(t.args) == 2:
            a = _eval(t.args[0], refvar, value)
            b = _eval(t.args[1], refvar, value)
            if not isinstance(a, int) or not isinstance(b, int) or b == 0:
                raise _Unevaluable()
            # Aeon integer ``/`` and ``%`` follow truncated (C-like) semantics;
            # Python's floor division differs on negatives, so compute via int().
            q = int(a / b)
            return q if op == "/" else a - b * q
        fn = _BINOPS.get(op)
        if fn is not None and len(t.args) == 2:
            return fn(_eval(t.args[0], refvar, value), _eval(t.args[1], refvar, value))
    raise _Unevaluable()
