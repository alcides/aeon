"""Example-driven (PBE) synthesis for the AFTA backend.

This is the BLAZE/SYNGAR construction (Wang, Dillig & Singh, POPL'18) specialised
to aeon: given a function hole ``def f (x:T) : U := ?hole`` decorated with
``@example(f in_i == out_i)`` input/output pairs, synthesise a body -- an
expression over the in-scope DSL components (e.g. the ``String`` library) -- that
reproduces every example.

The automaton is built bottom-up exactly like the concrete FTA: a *bank* of
sub-programs grown one operator deeper each round. A goal-typed candidate's
**concrete state** is the vector of values it produces on the example inputs
(evaluated in-process by the ``pbe_probe`` the entrypoint installs). Two
candidates with the same output vector are observationally equivalent and merged
-- the version-space compression that makes the search tractable.

On top of this concrete automaton sits AFTA's **predicate abstraction + CEGAR**.
The abstract state is the truth-vector of an active predicate set ``P`` over the
output vector; ``P`` starts coarse (empty -> every output collapses to one
state) and is refined one predicate at a time whenever an abstractly-accepting
candidate fails the concrete check (exact match against the expected outputs).
The predicate hierarchy, coarse to fine, is: per-example *length agreement*,
then per-example *exact agreement*. Once every exact-agreement predicate is
active the abstraction is precise, so the loop converges; soundness never rests
on the abstraction, since acceptance is always the concrete exact-match check.
"""

from __future__ import annotations

import random
import time
from typing import Any, Callable, Optional

from loguru import logger

from aeon.core.terms import Literal, Term
from aeon.core.types import Type, t_int
from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.modules.fta.synthesizer import _freeze, _term_size
from aeon.synthesis.modules.symetric.synthesizer import base_key
from aeon.typechecking.context import TypingContext

# A predicate maps a candidate's output vector to a bool (its abstract bit).
Predicate = Callable[[tuple], bool]


def _length(v: Any) -> Optional[int]:
    try:
        return len(v)
    except Exception:
        return None


def has_io_examples(metadata: dict, fun_name) -> bool:
    entry = metadata.get(fun_name, {})
    return bool(entry.get("io_examples")) and entry.get("pbe_probe") is not None


def synthesize_pbe(
    synth,
    ctx: TypingContext,
    type: Type,
    fun_name,
    metadata: dict,
    deadline: float,
    start: float,
    ui,
    validate: Callable[[Term], bool],
) -> Term:
    """Bottom-up PBE synthesis with predicate-abstraction CEGAR over the example
    output vectors. ``synth`` is the owning AFTASynthesizer (for ``_collect`` /
    ``_combos`` and the bank-size knobs)."""
    rnd = random.Random(synth.seed)
    # Observational merging keeps the bank small, so we can afford to enumerate
    # transitions exhaustively (rather than sampling under a tight cap) -- this
    # is what makes the CFTA find e.g. ``slice name 0 3`` deterministically.
    synth.combo_cap = max(synth.combo_cap, 200000)
    synth.max_bank = max(synth.max_bank, 100000)
    entry = metadata.get(fun_name, {})
    io_examples: list[tuple[list, Any]] = entry["io_examples"]
    probe: Callable[[Term, list], Any] = entry["pbe_probe"]
    expected: tuple = tuple(_freeze(out) for (_inp, out) in io_examples)
    inputs: list[list] = [inp for (inp, _out) in io_examples]
    n = len(io_examples)

    builders, atoms = synth._collect(ctx, synth._inst_types(type), fun_name)
    goal_key = base_key(type)
    int_key = base_key(t_int)

    # Output vector of a goal-typed candidate, or None if it cannot be run on
    # every example (a partial/crashing program -- never a solution).
    out_cache: dict[str, Optional[tuple]] = {}

    def outputs(term: Term) -> Optional[tuple]:
        k = str(term)
        if k in out_cache:
            return out_cache[k]
        vec: list = []
        for inp in inputs:
            try:
                # Freeze to a hashable form (lists/sets become tuples/frozensets)
                # so the output vector can key the observational-equivalence map.
                vec.append(_freeze(probe(term, inp)))
            except Exception:
                out_cache[k] = None
                return None
        res = tuple(vec)
        out_cache[k] = res
        return res

    # The concrete acceptance oracle: the candidate reproduces every example.
    def solves(term: Term) -> bool:
        return outputs(term) == expected

    # Predicate hierarchy (coarse -> fine), generated lazily per example.
    def len_pred(i: int) -> Predicate:
        return lambda vec: _length(vec[i]) == _length(expected[i])

    def eq_pred(i: int) -> Predicate:
        return lambda vec: vec[i] == expected[i]

    predicate_pool: list[Predicate] = [len_pred(i) for i in range(n)] + [eq_pred(i) for i in range(n)]
    active: list[int] = []  # indices into predicate_pool

    def signature(vec: tuple) -> tuple:
        return tuple(predicate_pool[i](vec) for i in active)

    def abstractly_accepting(vec: tuple) -> bool:
        # A state is abstractly accepting when every active predicate holds.
        return all(predicate_pool[i](vec) for i in active)

    # -- bottom-up CFTA bank, compressed by observational equivalence ----------
    # Each (type, output-vector) class keeps a single smallest representative:
    # this is the version-space compression that makes bottom-up enumeration
    # tractable. A term that cannot be run on every example is dropped.
    bank: dict[str, list[Term]] = {}
    seen: dict[str, set[str]] = {}  # syntactic dedup (cheap pre-filter)
    obs_rep: dict[str, dict[tuple, Term]] = {}  # type -> output-vector -> rep
    goal_terms: list[Term] = []

    def add_bank(key: str, terms: list[Term]) -> None:
        b = bank.setdefault(key, [])
        s = seen.setdefault(key, set())
        reps = obs_rep.setdefault(key, {})
        for t in terms:
            k = str(t)
            if k in s:
                continue
            s.add(k)
            vec = outputs(t)
            if vec is None:
                continue  # not runnable on the examples -- not a usable state
            prev = reps.get(vec)
            if prev is not None:
                # Observationally equivalent to an existing term; keep smaller.
                if _term_size(t) < _term_size(prev):
                    reps[vec] = t
                continue
            reps[vec] = t
            b.append(t)
            if key == goal_key:
                goal_terms.append(t)
        if len(b) > synth.max_bank:
            del b[synth.max_bank :]

    for key, vs in atoms.items():
        add_bank(key, list(vs))

    # Integer leaves: string-DSL programs index/measure strings, so the useful
    # constants are small offsets bounded by the example lengths -- a far tighter
    # (and exhaustively enumerable) set than the spec-guided path's wide grid.
    max_len = 0
    for inp, out in io_examples:
        for v in list(inp) + [out]:
            if isinstance(v, str):
                max_len = max(max_len, len(v))
    int_vals = sorted(set(range(-1, max_len + 2)) | {0, 1, 2})
    add_bank(int_key, [Literal(v, t_int) for v in int_vals])

    # String constants: the empty string, the individual characters of the
    # outputs (inserted glyphs) AND of the inputs (separators a program splits
    # on -- " ", "-", "." -- almost always live in the inputs, not the output),
    # plus any whole expected output.
    str_consts: set[str] = {""}
    for out in expected:
        if isinstance(out, str):
            str_consts.add(out)
            str_consts.update(set(out))
    # From the inputs, only the separator-like (non-alphanumeric) characters --
    # " ", "-", ".", "," etc. These are what programs split on; seeding every
    # input character would bloat the leaf set on long inputs without helping.
    for inp in inputs:
        for v in inp:
            if isinstance(v, str):
                str_consts.update(c for c in v if not c.isalnum())
    if str_consts:
        from aeon.core.types import t_string

        add_bank(base_key(t_string), [Literal(s, t_string) for s in sorted(str_consts)])

    tried: set[str] = set()
    refinements = 0

    def cegar_pass() -> Optional[Term]:
        nonlocal refinements
        for _ in range(synth.max_refine + 1):
            if time.time() >= deadline:
                return None
            # Collapse goal terms into abstract states (smallest representative).
            states: dict[tuple, Term] = {}
            for t in goal_terms:
                if str(t) in tried:
                    continue
                vec = outputs(t)
                if vec is None:
                    tried.add(str(t))
                    continue
                if not abstractly_accepting(vec):
                    continue
                sig = signature(vec)
                cur = states.get(sig)
                if cur is None or _term_size(t) < _term_size(cur):
                    states[sig] = t
            candidates = sorted(states.values(), key=_term_size)
            refined = False
            for term in candidates:
                if time.time() >= deadline:
                    return None
                # Acceptance is example-consistency: the candidate reproduces
                # every I/O pair. We do NOT additionally require universal
                # refinement well-typedness -- a PBE program (e.g. one slicing
                # ``name`` at a fixed index) need only be correct on the given
                # inputs, exactly as in BLAZE. ``validate`` is left as an
                # optional soft check, never a gate.
                if solves(term):
                    return term
                tried.add(str(term))
                # Spurious abstract acceptance: refine on a predicate this
                # candidate violates (an example it gets wrong), coarsest first.
                vec = outputs(term)
                new = _first_violated(predicate_pool, active, vec)
                if new is not None:
                    active.append(new)
                    refinements += 1
                    refined = True
                    break
            if not refined:
                return None
        return None

    # Depth is bounded by the time budget (and a fixpoint, when a full round adds
    # no new terms), not a fixed number of rounds; ``synth.rounds``, when set,
    # caps it explicitly. ``rounds`` defaults to ``None`` (unbounded), so a plain
    # ``range(synth.rounds)`` would crash -- deepen with a budget-guarded loop
    # mirroring the non-PBE path.
    solution = cegar_pass()
    depth = 0
    while solution is None and time.time() < deadline:
        if synth.rounds is not None and depth >= synth.rounds:
            break
        before = sum(len(v) for v in bank.values())
        snapshot = {k: list(v) for k, v in bank.items()}
        for comps in builders.values():
            for comp in comps:
                if time.time() >= deadline:
                    break
                add_bank(comp.ret_key, synth._combos(comp, snapshot, deadline, rnd))
        solution = cegar_pass()
        depth += 1
        if sum(len(v) for v in bank.values()) == before:
            break

    if solution is not None:
        ui.register(solution, [0.0], time.time() - start, True)
        logger.log(
            "SYNTHESIZER",
            f"afta(pbe): solution consistent with all {n} example(s) found; "
            f"{refinements} abstraction refinement(s), {len(goal_terms)} goal terms enumerated.",
        )
        return solution
    raise SynthesisNotSuccessful(
        f"afta(pbe): no program consistent with all {n} example(s) found within the budget "
        f"(reached depth {depth}, enumerated {len(goal_terms)} goal terms, {refinements} refinements). "
        "Try a larger budget, more rounds, or a richer DSL in scope."
    )


def _first_violated(pool: list[Predicate], active: list[int], vec: tuple) -> Optional[int]:
    """The index of the coarsest pool predicate not yet active that ``vec``
    violates -- the CEGAR refinement that splits the offending state."""
    for i, pred in enumerate(pool):
        if i in active:
            continue
        try:
            if not pred(vec):
                return i
        except Exception:
            continue
    return None
