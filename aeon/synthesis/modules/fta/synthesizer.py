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

from aeon.core.terms import (
    Abstraction,
    Application,
    If,
    Let,
    Literal,
    Rec,
    RefinementAbstraction,
    Term,
    TypeAbstraction,
    TypeApplication,
    Var,
)
from aeon.core.types import (
    AbstractionType,
    Type,
    TypeConstructor,
    TypePolymorphism,
    t_bool,
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
    is_if: bool = False  # build If(cond, then, else) rather than an application


class FTASynthesizer(Synthesizer):
    """Component-based synthesis by building a finite tree automaton bottom-up
    and extracting the smallest spec-consistent program from it."""

    # Stashed in ``computations`` (called before ``synthesize``) so example-driven
    # runs can evaluate candidate sub-programs on concrete @example/@csv inputs,
    # in the program's context (top-level defs / library primitives in scope).
    _ectx: Optional[EvaluationContext] = None
    _replace: Optional[Callable[[Term], Term]] = None

    def computations(self, primitives: Any) -> dict[str, Any]:
        # The automaton keys states by each candidate's concrete *output*; the
        # pool computes it (a ``@cluster`` featuriser, else the candidate value).
        self._ectx = primitives.ectx
        self._replace = primitives.replace
        return {"output": primitives.feature}

    def __init__(
        self,
        seed: int = 0,
        int_lo: int = -8,
        int_hi: int = 33,
        rounds: int = 3,
        combo_cap: int = 4096,
        max_bank: int = 512,
        if_branch_cap: int = 20,
        enable_if: bool = True,
    ):
        self.seed = seed
        self.int_lo = int_lo
        self.int_hi = int_hi
        self.rounds = rounds
        self.combo_cap = combo_cap
        self.max_bank = max_bank
        # Whether to offer the conditional builder. Off avoids its cost/overfit
        # when the target is known to be branch-free.
        self.enable_if = enable_if
        # then/else branches are restricted to the smallest reps so the
        # conditional builder enumerates a bounded space (the condition pool is
        # already tiny after observational compression).
        self.if_branch_cap = if_branch_cap

    # -- components -----------------------------------------------------------

    def _collect(
        self, ctx: TypingContext, inst_types: set[TypeConstructor], fun_name: Name
    ) -> tuple[dict[str, list[_MonoComponent]], dict[str, list[Var]]]:
        """Index the in-scope bindings as builders (functions/constructors, the
        automaton's ranked alphabet) and atoms (nullary leaves). Polymorphic
        operators (``+``/``*``/… : ``∀a. a -> a -> a``) are monomorphized at
        ``inst_types`` so the search can build functions of the input over them.
        The function being synthesized (no self-recursion) and the ``native``
        intrinsics are skipped, as in the grammar backend."""
        from aeon.synthesis.grammar.grammar_generation import monomorphize_poly_type

        skip_names = {fun_name.name, "native", "native_import", "print"}
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
            if name.name in skip_names:
                continue
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
        for idx, ak in enumerate(comp.arg_keys):
            pool = bank.get(ak, [])
            if not pool:
                return []
            if comp.is_if and idx >= 1:
                # then/else: only the smallest representatives, so the product
                # stays bounded and is enumerated exhaustively (below).
                pool = sorted(pool, key=_term_size)[: self.if_branch_cap]
            pools.append(pool)
        total = 1
        for p in pools:
            total *= len(p)
        # The conditional's space is already bounded by the branch cap, so
        # enumerate it fully rather than sampling.
        cap = max(self.combo_cap, total) if comp.is_if else self.combo_cap

        def build(choice: tuple[Term, ...]) -> Term:
            # If(cond, then, else) for the conditional builder; otherwise an
            # application of the (possibly type-applied) component to its args.
            if comp.is_if:
                return If(choice[0], choice[1], choice[2])
            term = self._head(comp)
            for a in choice:
                term = Application(term, a)
            return term

        out: list[Term] = []
        if total <= cap:
            for choice in itertools.product(*pools):
                if time.time() >= deadline:
                    break
                out.append(build(choice))
        else:
            for _ in range(cap):
                out.append(build(tuple(rnd.choice(p) for p in pools)))
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

        # Instantiate polymorphic operators at the goal type (so arithmetic over
        # the input can be built) plus Int (for indices/literals). Keeping the set
        # minimal avoids a blow-up of useless cross-type builders.
        inst_types: set[TypeConstructor] = {t_int}
        _gret = _peel(type)[1]
        if isinstance(_gret, TypeConstructor):
            inst_types.add(_gret)

        builders, atoms = self._collect(ctx, inst_types, fun_name)
        goal_key = base_key(type)
        int_key = base_key(t_int)
        float_key = base_key(t_float)
        bool_key = base_key(t_bool)

        # A conditional builder: If(cond:Bool, then:T, else:T) -> T at the goal
        # type. Lets the FTA synthesize branching programs (the paper's switch /
        # fallback), keyed by the branch's observed output like any other state.
        # Prepended so it is explored first each round, before the wide arithmetic.
        if self.enable_if:
            builders.setdefault(goal_key, []).insert(
                0, _MonoComponent(Name("if", 0), (bool_key, goal_key, goal_key), goal_key, is_if=True)
            )
        else:
            # Without the conditional, Bool sub-programs have no consumer at the
            # goal type, so don't waste the search generating them.
            builders.pop(bool_key, None)

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

        # In example mode, restrict the symbolic operators to the additive and
        # boolean ones (data-completion formulas are SUM/MINUS/COUNT-shaped);
        # dropping ``*``/``/``/``%``/… curbs the bottom-up combinatorial blow-up
        # while leaving the table primitives (alphabetic names) untouched.
        if example_mode:
            allowed_ops = {"+", "-", "==", "!=", "<", "<=", ">", ">=", "&&", "||", "-->", "!"}
            for _k in list(builders.keys()):
                builders[_k] = [
                    c
                    for c in builders[_k]
                    if not (_is_symbolic_op(c.name.pretty()) and c.name.pretty() not in allowed_ops)
                ]
        # Evaluation context with the program's top-level defs (library
        # primitives, table globals) bound once, so candidate sub-programs are
        # observed in the program's context. Falls back to the bare context.
        eval_ectx = self._ectx
        if example_mode and self._replace is not None and self._ectx is not None:
            try:
                eval_ectx = _bound_context(self._replace(Literal(0, t_int)), self._ectx)
            except Exception:
                eval_ectx = self._ectx

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
                # Evaluate in the program's context (top-level defs pre-bound in
                # eval_ectx), the param already substituted away.
                try:
                    outs.append(_freeze(aeon_eval(sub, eval_ectx)))
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
                if example_mode:
                    # Examples are the spec: check the cheap observational match
                    # first, and only run the (SMT-backed) type check on the few
                    # candidates that already reproduce every example.
                    validated[st] = matches_examples(st) and _safe(validate, rep[st])
                else:
                    validated[st] = _safe(validate, rep[st])
            if validated[st]:
                cand = rep[st]
                if best is None or _term_size(cand) < _term_size(best):
                    best = cand
                    ui.register(best, [0.0], time.time() - start, True)

        bank: dict[str, list[Term]] = {}
        seen: dict[str, set[str]] = {}  # non-example mode: syntactic dedup
        bank_states: dict[str, dict[Any, Term]] = {}  # example mode: state -> rep

        def add_bank(key: str, terms: list[Term]) -> None:
            b = bank.setdefault(key, [])
            if example_mode:
                # Observational-equivalence compression at *every* type (the FTA's
                # core idea): keep one representative per distinct output vector
                # over the examples, so the version space stays small. Sub-terms
                # that cannot be evaluated cannot be a state, so are dropped.
                states = bank_states.setdefault(key, {})
                for t in terms:
                    if time.time() >= deadline:
                        break
                    st = obs_examples(t)
                    if st[0] != "vec":
                        continue
                    vec = st[1]
                    prev = states.get(vec)
                    if prev is None:
                        states[vec] = t
                        b.append(t)
                    elif _term_size(t) < _term_size(prev):
                        states[vec] = t
                        b[b.index(prev)] = t
                    if key == goal_key:
                        insert_goal(t)
                return
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

        # Round 0 -- nullary leaves: the in-scope atoms, plus a literal range.
        # In example mode a small set suffices (and stays observationally compact);
        # constant-refinement mode needs the wide range to hit a specific value.
        int_lits: Any = (0, 1, 2) if example_mode else range(self.int_lo, self.int_hi)
        for key, vs in atoms.items():
            add_bank(key, list(vs))
        add_bank(int_key, [Literal(v, t_int) for v in int_lits])
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


def _is_symbolic_op(name: str) -> bool:
    """Whether ``name`` is a symbolic operator (``+``, ``*``, ``&&``) rather than
    an alphanumeric identifier (a library primitive like ``prev_nonmissing``)."""
    return bool(name) and all(not c.isalnum() and c != "_" for c in name)


def _bound_context(prog: Term, ectx):
    """Bind every top-level ``let``/``rec`` of ``prog`` into ``ectx`` *once*,
    mirroring the evaluator, so candidate sub-programs can then be evaluated in
    a single step (with library primitives and table globals already in scope)
    instead of re-binding the whole chain per evaluation."""
    cur = prog
    e = ectx
    while isinstance(cur, (Let, Rec)):
        if isinstance(cur, Let):
            e = e.with_var(cur.var_name, aeon_eval(cur.var_value, e))
        else:
            inner = cur.var_value
            while isinstance(inner, (TypeAbstraction, RefinementAbstraction)):
                inner = inner.body
            if isinstance(inner, Abstraction):
                # Recursion-tying closure (as in the evaluator): captures the
                # context at this binding plus itself.
                def make(fun: Abstraction, base, name: Name):
                    def v(x):
                        return aeon_eval(fun.body, base.with_var(name, v).with_var(fun.var_name, x))

                    return v

                e = e.with_var(cur.var_name, make(inner, e, cur.var_name))
            else:
                rec_ctx = e.with_var(cur.var_name, None)
                e = rec_ctx.with_var(cur.var_name, aeon_eval(cur.var_value, rec_ctx))
        cur = cur.body
    return e


def _example_literal(value: float, ty: Type) -> Optional[Term]:
    """A core literal of ``ty`` for a numeric example value, or ``None`` when the
    parameter type is not Int/Float (so example mode does not apply)."""
    key = base_key(ty)
    if key == base_key(t_int):
        return Literal(int(value), t_int)
    if key == base_key(t_float):
        return Literal(float(value), t_float)
    return None
