"""BFS-based type-directed synthesizer.

Starts from a hole of the target type and grows complete terms
depth-by-depth. The only bound is the wall-clock ``budget``; there's
no static depth cap.

Per-candidate pipeline:

1. expand the first unfilled hole into all backward/forward action
   results;
2. if all remaining holes are leaf-solvable, hand them to SMT
   (``solve_literals``) to obtain a concrete term;
3. fill any remaining ``Annotation(Hole, T)`` placeholders with
   canonical seeds (via ``smt_holes``-style fallback inside
   ``_try_complete``) — actually done by ``solve_literals`` and
   ``_extract_solution``;
4. validate (typecheck against the hole's expected type), evaluate
   the multi-objective fitness, and offer to a Pareto front with
   ε-dominance;
5. when the budget runs out, return the min-sum representative of the
   front.
"""

from __future__ import annotations

import threading
from collections import deque
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from time import monotonic_ns
from typing import Callable

from loguru import logger

from aeon.core.terms import Abstraction, Term
from aeon.core.types import AbstractionType, Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer, SynthesisNotSuccessful
from aeon.synthesis.modules.tdsyn.actions import backward_candidates, forward_candidates
from aeon.synthesis.modules.tdsyn.helpers import make_skip_fn
from aeon.synthesis.modules.tdsyn.smt_solve import all_leaf_holes, solve_literals
from aeon.synthesis.modules.tdsyn.worklist import PartialAST, TypedHole, fresh_hole, substitute_hole
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name

_loc = SynthesizedLocation("tdsyn")

# Default ε for the dominance filter. 0.0 = strict Pareto (no information loss);
# any positive value collapses near-duplicate points to bound the front size.
DEFAULT_EPSILON = 0.0


Front = list[tuple[list[float], Term]]


def _eps_dominates(a: list[float], b: list[float], eps: float) -> bool:
    """Strict ε-dominance: ``a`` is no more than ε worse than ``b`` on any
    axis, and more than ε better on at least one. Both score vectors must
    have the same length."""
    if len(a) != len(b):
        return False
    strictly_better = False
    for x, y in zip(a, b):
        if x > y + eps:
            return False
        if x < y - eps:
            strictly_better = True
    return strictly_better


def _front_offer(front: Front, score: list[float], term: Term, eps: float) -> bool:
    """Offer ``(score, term)`` to the Pareto front.

    Rejects if any existing point ε-dominates the candidate or is within ε
    on every axis (ε-equality is treated as a near-duplicate). Otherwise
    evicts every existing point ε-dominated by the candidate, appends the
    new point, and returns True. Mutates ``front`` in place.
    """
    for s, _ in front:
        if _eps_dominates(s, score, eps):
            return False
        if all(abs(x - y) <= eps for x, y in zip(s, score)):
            return False
    front[:] = [(s, t) for s, t in front if not _eps_dominates(score, s, eps)]
    front.append((score, term))
    return True


def _select_from_front(front: Front) -> Term | None:
    """Pick a representative term from the Pareto front.

    Min sum-of-scores favours generalists (low on every axis) over
    specialists that ace a few axes by being trivial.
    """
    if not front:
        return None
    return min(front, key=lambda st: sum(st[0]))[1]


def _get_elapsed_time(start_time: int) -> float:
    return (monotonic_ns() - start_time) * 0.000000001


def _peel_abstractions(ty: Type, ctx: TypingContext) -> tuple[Term, Type, TypingContext, list[TypedHole]]:
    """If the target type is a function type, peel off abstractions.

    Returns (wrapper_term_with_hole, inner_type, extended_ctx, [inner_hole]).
    For non-function types, returns a single hole.
    """
    if not isinstance(ty, AbstractionType):
        hole_term, typed_hole = fresh_hole(ty, ctx)
        return hole_term, ty, ctx, [typed_hole]

    current_type: Type = ty
    current_ctx = ctx
    var_names: list[Name] = []

    while isinstance(current_type, AbstractionType):
        var_names.append(current_type.var_name)
        current_ctx = current_ctx.with_var(current_type.var_name, current_type.var_type)
        current_type = current_type.type

    inner_hole_term, inner_typed_hole = fresh_hole(current_type, current_ctx)

    term: Term = inner_hole_term
    for var_name in reversed(var_names):
        term = Abstraction(var_name, term, _loc)

    return term, current_type, current_ctx, [inner_typed_hole]


class TDSynSynthesizer(Synthesizer):
    """BFS-based type-directed synthesizer.

    Grows complete terms depth-by-depth from a hole of the target type.
    SMT-aware leaf completion when refinements pin literal values;
    falls back to canonical seeds otherwise. Pareto front with
    ε-dominance for multi-objective fitness.

    ``parallel`` controls how many complete candidates are evaluated
    concurrently via a :class:`ThreadPoolExecutor`. The actual fitness
    evaluation spawns a subprocess per call (in ``make_evaluator``), so N
    threads each waiting on their own subprocess gives real wall-clock
    parallelism — the GIL is released during ``Process.join``. Set to 1
    for the strictly sequential search.
    """

    def __init__(self, epsilon: float = DEFAULT_EPSILON, parallel: int = 1):
        assert epsilon >= 0.0
        assert parallel >= 1
        self.epsilon = epsilon
        self.parallel = parallel

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
        assert isinstance(ctx, TypingContext)
        assert isinstance(type, Type)

        skip = make_skip_fn(fun_name, metadata)
        self._has_goals = bool(metadata.get(fun_name, {}).get("goals"))
        start_time = monotonic_ns()
        front: Front = []
        front_lock = threading.Lock()
        ui.register(None, None, 0, True)

        initial_term, _, _, initial_holes = _peel_abstractions(type, ctx)
        worklist: deque[PartialAST] = deque(
            [PartialAST(term=initial_term, holes=initial_holes, depth=0)]
        )

        if self.parallel > 1:
            return self._parallel_search(
                worklist, validate, evaluate, skip, start_time, budget, ui, front, front_lock,
            )

        # Sequential path — fully unchanged behaviour.
        while worklist and _get_elapsed_time(start_time) < budget:
            partial = worklist.popleft()

            if partial.is_complete():
                front = self._try_complete(partial, validate, evaluate, start_time, ui, front, front_lock)
                if not self._has_goals and front:
                    return front[0][1]
                continue

            # Try SMT completion if every remaining hole is leaf-solvable.
            front, _smt_ok = self._try_smt_complete(partial, validate, evaluate, start_time, ui, front, front_lock)

            # Otherwise expand the first hole and queue every child.
            hole = partial.holes[0]
            for child in self._expand_hole(partial, hole, skip):
                if child.is_complete():
                    front = self._try_complete(child, validate, evaluate, start_time, ui, front, front_lock)
                    if not self._has_goals and front:
                        return front[0][1]
                else:
                    front, smt_ok = self._try_smt_complete(child, validate, evaluate, start_time, ui, front, front_lock)
                    if not smt_ok:
                        worklist.append(child)

        chosen = _select_from_front(front)
        if chosen is not None:
            return chosen
        raise SynthesisNotSuccessful("TDSynSynthesizer: no valid candidate found within budget")

    def _parallel_search(
        self,
        worklist: "deque[PartialAST]",
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        skip: Callable[[Name], bool],
        start_time: int,
        budget: float,
        ui: SynthesisUI,
        front: Front,
        front_lock: threading.Lock,
    ) -> Term:
        """BFS with parallel evaluation of complete candidates.

        Expansion / SMT are run on the main thread (cheap). Validate + evaluate
        of fully-complete candidates is submitted to a ``ThreadPoolExecutor``
        of size ``self.parallel``; the main loop keeps the pool fed while
        reaping completed futures and continues expanding partials.
        """
        pending: set = set()
        with ThreadPoolExecutor(max_workers=self.parallel) as executor:
            def submit(p: PartialAST) -> None:
                fut = executor.submit(
                    self._try_complete, p, validate, evaluate, start_time, ui, front, front_lock,
                )
                pending.add(fut)

            while (worklist or pending) and _get_elapsed_time(start_time) < budget:
                # Fan out: submit work until we've saturated the pool's queue.
                while worklist and len(pending) < self.parallel * 2:
                    if _get_elapsed_time(start_time) >= budget:
                        break
                    partial = worklist.popleft()
                    if partial.is_complete():
                        submit(partial)
                        continue
                    front, _smt_ok = self._try_smt_complete(
                        partial, validate, evaluate, start_time, ui, front, front_lock,
                    )
                    hole = partial.holes[0]
                    for child in self._expand_hole(partial, hole, skip):
                        if child.is_complete():
                            submit(child)
                        else:
                            front, smt_ok = self._try_smt_complete(
                                child, validate, evaluate, start_time, ui, front, front_lock,
                            )
                            if not smt_ok:
                                worklist.append(child)

                # Reap whatever finished while we were fanning out.
                if pending:
                    done, still = wait(pending, timeout=0.05, return_when=FIRST_COMPLETED)
                    pending = set(still)
                    for fut in done:
                        try:
                            fut.result()
                        except Exception as e:
                            logger.debug(f"tdsyn parallel eval failed: {e}")
                        if not self._has_goals:
                            with front_lock:
                                if front:
                                    # Drain remaining pending without blocking the return.
                                    for f in pending:
                                        f.cancel()
                                    return front[0][1]

            # Out of budget or work. Cancel anything still pending, then pick.
            for f in pending:
                f.cancel()

        chosen = _select_from_front(front)
        if chosen is not None:
            return chosen
        raise SynthesisNotSuccessful("TDSynSynthesizer: no valid candidate found within budget")

    def _try_complete(
        self,
        partial: PartialAST,
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        start_time: int,
        ui: SynthesisUI,
        front: Front,
        front_lock: threading.Lock,
    ) -> Front:
        """Try to validate and evaluate a complete term, offering it to the front.

        Thread-safe under ``front_lock`` — multiple workers may call this
        concurrently. The expensive ``validate`` / ``evaluate`` calls
        themselves run outside the lock; only the front update is guarded.
        """
        if not partial.is_complete():
            return front
        term = partial.term
        try:
            if validate(term):
                if not self._has_goals:
                    with front_lock:
                        if not front:
                            front.append(([], term))
                    ui.register(term, [], _get_elapsed_time(start_time), True)
                    return front
                score = evaluate(term)
                with front_lock:
                    added = _front_offer(front, score, term, self.epsilon)
                ui.register(term, score, _get_elapsed_time(start_time), added)
            else:
                ui.register(term, "Invalid", _get_elapsed_time(start_time), False)
        except Exception:
            ui.register(term, "Invalid", _get_elapsed_time(start_time), False)
        return front

    def _try_smt_complete(
        self,
        partial: PartialAST,
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        start_time: int,
        ui: SynthesisUI,
        front: Front,
        front_lock: threading.Lock,
    ) -> tuple[Front, bool]:
        """If every remaining hole is leaf-solvable, ask SMT for a value
        per hole, substitute, and try-complete the resulting term(s).

        Returns ``(front, smt_succeeded)``; ``smt_succeeded`` is True if
        SMT produced at least one solution attempt, even if validation
        rejected it. When True, the caller should not re-enqueue the
        partial — SMT has spoken for this shape.
        """
        if not partial.holes or not all_leaf_holes(partial.holes):
            return front, False

        solutions = solve_literals(partial.holes)
        if not solutions:
            return front, False

        for solution in solutions:
            term = partial.term
            for hole_name, literal_term in solution.items():
                term = substitute_hole(term, hole_name, literal_term)
            front = self._try_complete(
                PartialAST(term=term, holes=[], depth=partial.depth),
                validate,
                evaluate,
                start_time,
                ui,
                front,
                front_lock,
            )

        return front, True

    def _expand_hole(
        self,
        partial: PartialAST,
        hole: TypedHole,
        skip: Callable[[Name], bool],
    ) -> list[PartialAST]:
        """Expand a single hole via backward + forward actions.

        No depth cap — only the outer time budget bounds the search.
        Returns children in deterministic action order; BFS over them
        gives a depth-by-depth visit.
        """
        results: list[PartialAST] = []
        for action_fn in (backward_candidates, forward_candidates):
            try:
                candidates = action_fn(hole, skip)
            except Exception as e:
                logger.debug(f"tdsyn: action failed: {e}")
                continue
            for replacement, new_holes in candidates:
                new_term = substitute_hole(partial.term, hole.name, replacement)
                remaining = [h for h in partial.holes if h.name != hole.name]
                remaining.extend(new_holes)
                new_depth = partial.depth + (1 if new_holes else 0)
                results.append(PartialAST(term=new_term, holes=remaining, depth=new_depth))
        return results
