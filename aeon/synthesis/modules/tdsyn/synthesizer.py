from __future__ import annotations

import random
from collections import deque
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

MAX_DEPTH = 5

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

    # Peel all abstractions
    current_type: Type = ty
    current_ctx = ctx
    var_names: list[Name] = []

    while isinstance(current_type, AbstractionType):
        var_names.append(current_type.var_name)
        current_ctx = current_ctx.with_var(current_type.var_name, current_type.var_type)
        current_type = current_type.type

    # Create the innermost hole
    inner_hole_term, inner_typed_hole = fresh_hole(current_type, current_ctx)

    # Wrap in abstractions (inside-out)
    term: Term = inner_hole_term
    for var_name in reversed(var_names):
        term = Abstraction(var_name, term, _loc)

    return term, current_type, current_ctx, [inner_typed_hole]


class TDSynSynthesizer(Synthesizer):
    """Type-directed synthesizer using backward and forward actions with SMT-based subtyping.

    Supports both enumerative (BFS) and random exploration modes.
    Loops until the time budget is exhausted, restarting with shuffled expansion
    order on each iteration to explore different term structures.
    """

    def __init__(self, mode: str = "enumerative", epsilon: float = DEFAULT_EPSILON):
        assert mode in ("enumerative", "random")
        assert epsilon >= 0.0
        self.mode = mode
        self.epsilon = epsilon
        self._rng = random.Random(42)
        self._iteration = 0

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
        ui.register(None, None, 0, True)

        # Peel abstractions from the target type
        initial_term, inner_type, inner_ctx, initial_holes = _peel_abstractions(type, ctx)

        initial_partial = PartialAST(term=initial_term, holes=initial_holes, depth=0)

        # Loop: restart search when worklist/walk is exhausted, until budget runs out
        while _get_elapsed_time(start_time) < budget:
            if self.mode == "enumerative":
                front = self._enumerative_search(initial_partial, skip, validate, evaluate, start_time, budget, ui, front)
            else:
                front = self._random_search(initial_partial, skip, validate, evaluate, start_time, budget, ui, front)
            # If no goals, return the first valid term found
            if not self._has_goals and front:
                return front[0][1]

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
    ) -> Front:
        """Try to validate and evaluate a complete term, offering it to the front."""
        if not partial.is_complete():
            return front
        term = partial.term
        try:
            if validate(term):
                if not self._has_goals:
                    if not front:
                        front.append(([], term))
                    ui.register(term, [], _get_elapsed_time(start_time), True)
                    return front
                score = evaluate(term)
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
    ) -> tuple[Front, bool]:
        """Try to complete a partial AST by solving all remaining holes with SMT.

        Returns (front, smt_succeeded). smt_succeeded is True if SMT produced
        at least one solution attempt (even if validation failed).
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

            complete = PartialAST(term=term, holes=[], depth=partial.depth)
            front = self._try_complete(complete, validate, evaluate, start_time, ui, front)

        return front, True

    def _expand_hole(
        self,
        partial: PartialAST,
        hole: TypedHole,
        skip: Callable[[Name], bool],
    ) -> list[PartialAST]:
        """Expand a single hole using backward and forward actions."""
        results: list[PartialAST] = []

        for action_fn in [backward_candidates, forward_candidates]:
            try:
                candidates = action_fn(hole, skip)
            except Exception as e:
                logger.debug(f"tdsyn: action failed: {e}")
                continue

            for replacement, new_holes in candidates:
                new_term = substitute_hole(partial.term, hole.name, replacement)
                remaining_holes = [h for h in partial.holes if h.name != hole.name]
                remaining_holes.extend(new_holes)
                new_depth = partial.depth + (1 if new_holes else 0)
                if new_depth <= MAX_DEPTH:
                    results.append(PartialAST(term=new_term, holes=remaining_holes, depth=new_depth))

        # Shuffle on non-first iterations to explore different orderings
        if self._iteration > 0 and results:
            self._rng.shuffle(results)

        return results

    def _enumerative_search(
        self,
        initial: PartialAST,
        skip: Callable[[Name], bool],
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        start_time: int,
        budget: float,
        ui: SynthesisUI,
        front: Front,
    ) -> Front:
        """BFS-based enumerative search."""
        self._iteration += 1
        worklist: deque[PartialAST] = deque([initial])

        while worklist:
            if _get_elapsed_time(start_time) > budget:
                break

            partial = worklist.popleft()

            if partial.is_complete():
                front = self._try_complete(partial, validate, evaluate, start_time, ui, front)
                continue

            # Try SMT completion if all holes are leaf-solvable
            front, _smt_ok = self._try_smt_complete(partial, validate, evaluate, start_time, ui, front)

            # Pick the first unfilled hole
            hole = partial.holes[0]
            expanded = self._expand_hole(partial, hole, skip)

            for new_partial in expanded:
                if _get_elapsed_time(start_time) > budget:
                    break
                if new_partial.is_complete():
                    front = self._try_complete(new_partial, validate, evaluate, start_time, ui, front)
                else:
                    # Try SMT on newly expanded partials too
                    front, smt_ok = self._try_smt_complete(
                        new_partial, validate, evaluate, start_time, ui, front
                    )
                    if not smt_ok:
                        worklist.append(new_partial)

        return front

    def _random_search(
        self,
        initial: PartialAST,
        skip: Callable[[Name], bool],
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        start_time: int,
        budget: float,
        ui: SynthesisUI,
        front: Front,
    ) -> Front:
        """Random exploration search."""
        rng = random.Random(42)

        while _get_elapsed_time(start_time) < budget:
            # Start fresh from initial each time for random search
            partial = PartialAST(term=initial.term, holes=list(initial.holes), depth=initial.depth)

            # Randomly expand holes until complete or stuck
            attempts = 0
            while not partial.is_complete() and attempts < MAX_DEPTH * 2:
                if _get_elapsed_time(start_time) > budget:
                    break

                # Try SMT completion first
                front, smt_ok = self._try_smt_complete(
                    partial, validate, evaluate, start_time, ui, front
                )
                if smt_ok:
                    break

                # Pick a random hole
                hole = rng.choice(partial.holes)

                # Get all candidates from both actions
                all_candidates: list[PartialAST] = self._expand_hole(partial, hole, skip)

                if not all_candidates:
                    break

                partial = rng.choice(all_candidates)
                attempts += 1

            if partial.is_complete():
                front = self._try_complete(partial, validate, evaluate, start_time, ui, front)

        return front
