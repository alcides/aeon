from __future__ import annotations

import random
from time import monotonic_ns
from typing import Callable

from loguru import logger

from aeon.core.terms import Abstraction, Term
from aeon.core.types import AbstractionType, Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer
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


def _is_better(v1: list[float], v2: list[float]) -> bool:
    if not v2:
        return True
    return all(x < y for x, y in zip(v1, v2))


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
    """Type-directed synthesizer using backward/forward actions, SMT subtyping, and random exploration."""

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
        start_time = monotonic_ns()
        best: tuple[list[float], Term | None] = ([], None)
        ui.register(None, None, 0, True)

        # Peel abstractions from the target type
        initial_term, inner_type, inner_ctx, initial_holes = _peel_abstractions(type, ctx)

        initial_partial = PartialAST(term=initial_term, holes=initial_holes, depth=0)

        best = self._random_search(initial_partial, skip, validate, evaluate, start_time, budget, ui, best)

        return best[1]

    def _try_complete(
        self,
        partial: PartialAST,
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        start_time: int,
        ui: SynthesisUI,
        best: tuple[list[float], Term | None],
    ) -> tuple[list[float], Term | None]:
        """Try to validate and evaluate a complete term."""
        if not partial.is_complete():
            return best
        term = partial.term
        try:
            if validate(term):
                score = evaluate(term)
                if _is_better(score, best[0]):
                    best = (score, term)
                    ui.register(term, score, _get_elapsed_time(start_time), True)
                else:
                    ui.register(term, score, _get_elapsed_time(start_time), False)
            else:
                ui.register(term, "Invalid", _get_elapsed_time(start_time), False)
        except Exception:
            ui.register(term, "Invalid", _get_elapsed_time(start_time), False)
        return best

    def _try_smt_complete(
        self,
        partial: PartialAST,
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        start_time: int,
        ui: SynthesisUI,
        best: tuple[list[float], Term | None],
    ) -> tuple[list[float], Term | None, bool]:
        """Try to complete a partial AST by solving all remaining holes with SMT.

        Returns (best, smt_succeeded). smt_succeeded is True if SMT produced
        at least one solution attempt (even if validation failed).
        """
        if not partial.holes or not all_leaf_holes(partial.holes):
            return best[0], best[1], False

        solutions = solve_literals(partial.holes)
        if not solutions:
            return best[0], best[1], False

        for solution in solutions:
            # Substitute all holes with their solved values
            term = partial.term
            for hole_name, literal_term in solution.items():
                term = substitute_hole(term, hole_name, literal_term)

            complete = PartialAST(term=term, holes=[], depth=partial.depth)
            best = self._try_complete(complete, validate, evaluate, start_time, ui, best)

        return best[0], best[1], True

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

        return results

    def _random_search(
        self,
        initial: PartialAST,
        skip: Callable[[Name], bool],
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        start_time: int,
        budget: float,
        ui: SynthesisUI,
        best: tuple[list[float], Term | None],
    ) -> tuple[list[float], Term | None]:
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
                best_score, best_term, smt_ok = self._try_smt_complete(
                    partial, validate, evaluate, start_time, ui, best
                )
                best = (best_score, best_term)
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
                best = self._try_complete(partial, validate, evaluate, start_time, ui, best)

        return best
