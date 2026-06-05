"""CATA: relational *recursive* synthesis via Constraint-Annotated Tree Automata.

Implements the line of Wang, Miltner, Dillig et al., "Relational Synthesis of
Recursive Programs via Constraint Annotated Tree Automata"
(https://www.cs.utexas.edu/~isil/cata.pdf) -- the third and most ambitious
backend on aeon's tree-automata line, after the concrete FTA (``fta``,
OOPSLA'17) and the abstraction-refinement AFTA (``afta``, POPL'18).

FTA and AFTA target **non-recursive** programs: they build an automaton over
component applications and accept the states consistent with a ground/abstract
spec. CATA extends tree-automata synthesis to **recursive** programs by letting
the automaton's positions carry **constraint annotations** -- relational
specifications relating a (possibly recursive) node's inputs to its output --
which are discharged with an SMT solver rather than by running the program on
ground examples.

How this maps onto aeon, and why it fits so cleanly:

* A function hole ``def f (x:T) : {v:U | R(x,v)} = ?hole`` is presented to the
  synthesiser with its abstractions already peeled: the goal is the *body* type
  ``{v:U | R(x,v)}`` (a relational refinement mentioning the parameter ``x``),
  with both ``x`` **and the recursive self-name ``f``** already in the context.
  So a recursive call is simply another component in the bottom-up bank.
* aeon's refinement types *are* relational specifications, and the liquid
  typechecker already performs exactly CATA's constraint discharge: it checks a
  recursive body against ``R`` using the **function's own signature as the
  inductive hypothesis** for the recursive call, and rejects it unless the
  recursion is **well-founded** (terminating). ``validate`` is therefore CATA's
  constraint-annotation oracle, for free.

What CATA adds over FTA/AFTA's construction:

1. **Monomorphic components from polymorphic library functions.** aeon's
   arithmetic/comparison operators (``+ - * == < <= > >=`` ...) are Num/Ord
   *typeclass methods* -- polymorphic, so FTA/AFTA's first-order component
   collection skips them. CATA instantiates them at the query's base types
   (reusing the ``lta`` backend's ``monomorphize``), so ``x - 1``, ``x == 0``,
   etc. become buildable.
2. **Conditional transitions** (``if c then t else e``) -- the base-case /
   recursive-case split that every interesting recursive definition needs.
3. **Recursive self-calls**, available as an ordinary component (above).

Acceptance is the constraint discharge: a goal-typed candidate is accepted iff
``validate`` proves its relational refinement under the inductive hypothesis and
termination. The smallest accepted program is returned. Like ``fta``/``afta``,
no ``@minimize``/``@maximize`` objective is required.

Scope. Recursive **datatype** synthesis (list/tree folds from the Synquid
suite) is the frontier this backend opens; convergence there is budget-bound and
a genuine search problem. The machinery here -- monomorphic operators,
conditionals, recursive self-calls, SMT constraint discharge -- is exactly what
that needs, and it already synthesises conditional and shallow recursive
integer programs end-to-end. Compression is by syntactic de-duplication of the
bank (each constraint-annotated state keeps its smallest representative);
merging states by *constraint equivalence* (an SMT entailment per pair) is the
faithful-but-costly refinement left as future work.

Selected with ``--synthesizer cata``.
"""

from __future__ import annotations

import itertools
import random
import time
from dataclasses import dataclass
from typing import Any, Callable, Optional

from loguru import logger

from aeon.core.terms import Abstraction, Application, If, Literal, Term, Var
from aeon.core.types import (
    AbstractionType,
    Type,
    TypePolymorphism,
    t_bool,
    t_int,
)
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer, SynthesisNotSuccessful
from aeon.synthesis.modules.fta.synthesizer import _safe, _term_size
from aeon.synthesis.modules.lta.polymorphism import (
    collect_type_universe,
    is_polymorphic,
    monomorphize,
)
from aeon.synthesis.modules.symetric.synthesizer import _peel, base_key
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name

_loc = SynthesizedLocation("cata")


@dataclass(frozen=True)
class Comp:
    """A component (constraint-annotated transition's label): a head term --
    ``Var(f)`` for a monomorphic binding or a ``TypeApplication`` nest for an
    instantiated polymorphic one -- with the base-type keys of its arguments and
    result. Unlike the first-order ``Component`` shared by ``fta``/``afta``, the
    head is a full ``Term`` so monomorphised (type-applied) operators qualify."""

    head: Term
    arg_keys: tuple[str, ...]
    ret_key: str


class CATASynthesizer(Synthesizer):
    """Recursive, relational component-based synthesis: build a tree automaton
    whose transitions include recursive self-calls and conditionals over
    monomorphised components, and accept states by SMT constraint discharge
    (the liquid typechecker)."""

    def computations(self, primitives: Any) -> dict[str, Any]:
        # Relational specs are universally quantified over the parameters, so
        # candidates cannot be observed on a single ground input; acceptance is
        # by SMT (validate), not by output value. Nothing extra to compute.
        return {}

    def __init__(
        self,
        seed: int = 0,
        int_lo: int = -2,
        int_hi: int = 5,
        rounds: int = 3,
        combo_cap: int = 2048,
        cond_cap: int = 4096,
        cond_head: int = 48,
        branch_head: int = 32,
        max_bank: int = 256,
        max_inst: int = 8,
    ):
        self.seed = seed
        self.int_lo = int_lo
        self.int_hi = int_hi
        self.rounds = rounds
        self.combo_cap = combo_cap
        self.cond_cap = cond_cap
        # How many of the smallest conditions / branches feed the (deterministic)
        # conditional enumeration -- bounds an otherwise cubic product.
        self.cond_head = cond_head
        self.branch_head = branch_head
        self.max_bank = max_bank
        self.max_inst = max_inst

    # -- component collection (monomorphising polymorphic bindings) ------------

    def _collect(self, ctx: TypingContext, universe: list[Type]) -> tuple[dict[str, list[Comp]], dict[str, list[Term]]]:
        """Index in-scope bindings as builders (the ranked alphabet, including
        recursive self-calls and monomorphised operators) and atoms (nullary
        leaves, including the function's parameters)."""
        builders: dict[str, list[Comp]] = {}
        atoms: dict[str, list[Term]] = {}

        def register(head: Term, ty: Type) -> None:
            arg_types, ret = _peel(ty)
            if any(isinstance(a, (AbstractionType, TypePolymorphism)) for a in arg_types):
                return  # no higher-order arguments
            if isinstance(ret, (AbstractionType, TypePolymorphism)):
                return
            ret_key = base_key(ret)
            if arg_types:
                comp = Comp(head, tuple(base_key(a) for a in arg_types), ret_key)
                builders.setdefault(ret_key, []).append(comp)
            else:
                atoms.setdefault(ret_key, []).append(head)

        for name, ty in ctx.concrete_vars():
            if is_polymorphic(ty):
                # Num/Ord operators and polymorphic library functions: make them
                # first-order by instantiating at the query's base types.
                for inst in monomorphize(name, ty, universe, max_instantiations=self.max_inst):
                    register(inst.term, inst.mono_type)
            else:
                register(Var(name), ty)
        return builders, atoms

    def _app_combos(self, comp: Comp, bank: dict[str, list[Term]], deadline: float, rnd: random.Random) -> list[Term]:
        """Application transitions ``comp(q1, ..., qk) -> q``: applications of
        ``comp`` whose arguments are drawn from the current bank per type."""
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
                term: Term = comp.head
                for a in choice:
                    term = Application(term, a)
                out.append(term)
        else:
            for _ in range(self.combo_cap):
                term = comp.head
                for p in pools:
                    term = Application(term, rnd.choice(p))
                out.append(term)
        return out

    def _cond_combos(
        self, bool_pool: list[Term], goal_pool: list[Term], deadline: float, rnd: random.Random
    ) -> list[Term]:
        """Conditional transitions ``if c then t else e -> q``: the base-case /
        recursive-case split. Deterministically enumerates the *smallest*
        conditions and branches first (bounded by ``cond_head``/``branch_head``),
        ordered by total node count, so the cheapest splits -- e.g.
        ``if x >= 0 then x else 0 - x`` -- are produced first and within
        ``cond_cap``, instead of being lost in a random sample of a huge
        product."""
        if not bool_pool or not goal_pool:
            return []
        conds = sorted(bool_pool, key=_term_size)[: self.cond_head]
        branches = sorted(goal_pool, key=_term_size)[: self.branch_head]
        triples = (
            (_term_size(c) + _term_size(t) + _term_size(e), c, t, e)
            for c in conds
            for t in branches
            for e in branches
            if t is not e
        )
        out: list[Term] = []
        for _size, c, t, e in sorted(triples, key=lambda x: x[0]):
            if time.time() >= deadline or len(out) >= self.cond_cap:
                break
            out.append(If(c, t, e, _loc))
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

        # Any abstractions still on the goal are peeled here (their binders join
        # the context); the synthesised body is re-wrapped before returning.
        body_type, ctx2, abs_names = _peel_abstractions(type, ctx)
        goal_key = base_key(body_type)
        bool_key = base_key(t_bool)
        int_key = base_key(t_int)

        universe = collect_type_universe(ctx2, body_type)
        builders, atoms = self._collect(ctx2, universe)

        bank: dict[str, list[Term]] = {}
        seen: dict[str, set[str]] = {}
        best: Optional[Term] = None
        validated_count = 0
        uses_recursion = False
        uses_conditional = False

        def wrap(body: Term) -> Term:
            term = body
            for name in reversed(abs_names):
                term = Abstraction(name, term, _loc)
            return term

        def consider(term: Term) -> None:
            """Validate a goal-typed candidate (the constraint-annotation
            discharge) and keep the smallest accepted one."""
            nonlocal best, validated_count, uses_recursion, uses_conditional
            validated_count += 1
            if _safe(validate, wrap(term)):
                if best is None or _term_size(term) < _term_size(best):
                    best = term
                    uses_recursion = _mentions(term, fun_name)
                    uses_conditional = _has_if(term)
                    ui.register(wrap(best), [0.0], time.time() - start, True)

        def add_bank(key: str, terms: list[Term]) -> None:
            b = bank.setdefault(key, [])
            s = seen.setdefault(key, set())
            for t in terms:
                k = str(t)
                if k in s:
                    continue
                s.add(k)
                b.append(t)
                if key == goal_key and best is None:
                    consider(t)
            if len(b) > self.max_bank:
                del b[self.max_bank :]

        # Round 0 -- nullary leaves: parameters and in-scope atoms, plus a small
        # integer grid (answers and numeric arguments / off-by-one constants).
        for key, vs in atoms.items():
            add_bank(key, list(vs))
        add_bank(int_key, [Literal(v, t_int) for v in range(self.int_lo, self.int_hi)])

        # Rounds 1..k -- grow the automaton one operator deeper each round:
        # application transitions (incl. recursive self-calls) and then the
        # conditional split. Stop as soon as a state is accepted.
        for _round in range(self.rounds):
            if best is not None or time.time() >= deadline:
                break
            snapshot = {k: list(v) for k, v in bank.items()}
            for comps in builders.values():
                for comp in comps:
                    if best is not None or time.time() >= deadline:
                        break
                    add_bank(comp.ret_key, self._app_combos(comp, snapshot, deadline, rnd))
            if best is not None or time.time() >= deadline:
                break
            # Conditionals at the goal type, using the bank grown so far.
            conds = self._cond_combos(bank.get(bool_key, []), bank.get(goal_key, []), deadline, rnd)
            add_bank(goal_key, conds)

        if best is not None:
            shape = []
            if uses_recursion:
                shape.append("recursive")
            if uses_conditional:
                shape.append("conditional")
            kind = "+".join(shape) if shape else "straight-line"
            ui.register(wrap(best), [0.0], time.time() - start, True)
            logger.log(
                "SYNTHESIZER",
                f"cata: {kind} solution found; discharged {validated_count} constraint-annotated "
                f"candidate(s) via the liquid typechecker (relational refinement + induction + termination).",
            )
            return wrap(best)
        raise SynthesisNotSuccessful(
            f"cata: no spec-consistent program of depth < {self.rounds} found within budget={budget}s "
            f"(discharged {validated_count} candidates). Try a larger budget, more rounds, or a wider "
            "integer grid; recursive-datatype goals may need a tailored component set."
        )


# -- free helpers ------------------------------------------------------------


def _peel_abstractions(ty: Type, ctx: TypingContext) -> tuple[Type, TypingContext, list[Name]]:
    """Strip any leading function arrows still on the goal type, extending the
    context with their binders. Holes are usually presented already peeled (the
    goal is the body type), so this is normally a no-op -- but it keeps CATA
    robust to multi-argument goals presented as a function type."""
    cur = ty
    cur_ctx = ctx
    names: list[Name] = []
    while isinstance(cur, AbstractionType):
        names.append(cur.var_name)
        cur_ctx = cur_ctx.with_var(cur.var_name, cur.var_type)
        cur = cur.type
    return cur, cur_ctx, names


def _mentions(term: Term, name: Name) -> bool:
    """Whether ``term`` references ``name`` (used to report recursion)."""
    if isinstance(term, Var):
        return term.name == name
    if isinstance(term, Application):
        return _mentions(term.fun, name) or _mentions(term.arg, name)
    if isinstance(term, If):
        return _mentions(term.cond, name) or _mentions(term.then, name) or _mentions(term.otherwise, name)
    if isinstance(term, Abstraction):
        return _mentions(term.body, name)
    return False


def _has_if(term: Term) -> bool:
    if isinstance(term, If):
        return True
    if isinstance(term, Application):
        return _has_if(term.fun) or _has_if(term.arg)
    if isinstance(term, Abstraction):
        return _has_if(term.body)
    return False
