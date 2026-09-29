"""Shared helpers for native grammar-search backends (no GeneticEngine).

Both :mod:`enumerative` and :mod:`random_search` expand Aeon's core term
grammar via the type-directed backward/forward actions and drive candidates
through the same validate / evaluate / Pareto archive loop.
"""

from __future__ import annotations

import random
from collections.abc import Callable, Iterator
from time import monotonic

from aeon.core.terms import Abstraction, Term
from aeon.core.types import AbstractionType, Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import InvalidIndividualException, TimeoutInEvaluationException
from aeon.synthesis.decorators import Goal
from aeon.synthesis.modules.tdsyn.actions import backward_candidates, forward_candidates
from aeon.synthesis.modules.tdsyn.helpers import clear_tdsyn_caches, make_skip_fn
from aeon.synthesis.modules.tdsyn.smt_solve import all_leaf_holes, solve_literals
from aeon.synthesis.modules.tdsyn.worklist import (
    Child,
    PartialAST,
    TypedHole,
    expand_at_hole,
    fresh_hole,
    substitute_holes_map,
)
from aeon.synthesis.pareto import (
    ParetoEntry,
    dominates,
    minimize_flags_from_goals,
    pick_pareto_member,
    update_pareto_front,
)
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name

# Bound recursive expansions so a single sample / worklist pass cannot grow
# without bound before the wall-clock budget ends.
MAX_DEPTH = 5

_loc = SynthesizedLocation("native_search")

__all__ = [
    "MAX_DEPTH",
    "ParetoEntry",
    "dominates",
    "drive_candidates",
    "expansions_for_hole",
    "initial_partial",
    "literal_completions",
    "make_skip",
    "minimize_flags_from_goals",
    "peel_abstractions",
    "pick_pareto_member",
    "sample_one",
    "update_pareto_front",
]


def peel_abstractions(ty: Type, ctx: TypingContext) -> tuple[Term, list[TypedHole]]:
    """Wrap a function goal as ``λ…λ.?hole`` and extend the context with binders."""
    if not isinstance(ty, AbstractionType):
        hole_term, typed_hole = fresh_hole(ty, ctx, path=())
        return hole_term, [typed_hole]

    current_type: Type = ty
    current_ctx = ctx
    var_names: list[Name] = []
    while isinstance(current_type, AbstractionType):
        var_names.append(current_type.var_name)
        current_ctx = current_ctx.with_var(current_type.var_name, current_type.var_type)
        current_type = current_type.type

    # Innermost hole sits under ``len(var_names)`` abstraction bodies.
    hole_path = tuple(Child.BODY for _ in var_names)
    inner_hole_term, inner_typed_hole = fresh_hole(current_type, current_ctx, path=hole_path)
    term: Term = inner_hole_term
    for var_name in reversed(var_names):
        term = Abstraction(var_name, term, _loc)
    return term, [inner_typed_hole]


def literal_completions(partial: PartialAST) -> list[Term]:
    """Complete a leaf-only partial term with each model supplied by Z3."""
    if not partial.holes or not all_leaf_holes(partial.holes):
        return []
    completed: list[Term] = []
    for solution in solve_literals(partial.holes):
        completed.append(substitute_holes_map(partial.term, solution))
    return completed


def expansions_for_hole(
    partial: PartialAST,
    hole: TypedHole,
    skip: Callable[[Name], bool],
    max_depth: int | None = None,
) -> list[PartialAST]:
    """Apply every grammar action to ``hole``.

    When ``max_depth`` is ``None``, recursive expansions are not depth-filtered
    (used by genetic programming so tree size can grow with the genome).
    """
    results: list[PartialAST] = []
    for action in (backward_candidates, forward_candidates):
        try:
            expansions = action(hole, skip)
        except Exception:
            # An action can be inapplicable to a particular dependent type;
            # the other grammar productions must remain available.
            continue
        for replacement, new_holes in expansions:
            depth = partial.depth + (1 if new_holes else 0)
            if max_depth is not None and depth > max_depth:
                continue
            results.append(expand_at_hole(partial, hole, replacement, new_holes, depth))
    return results


def sample_one(
    initial: PartialAST,
    skip: Callable[[Name], bool],
    rng: random.Random,
    max_depth: int = MAX_DEPTH,
    prefer_closed: bool = True,
) -> Term | None:
    """Grow one complete term by a random walk, or ``None`` if stuck.

    Used by :mod:`random_search` and by PBT value generation. When
    ``prefer_closed`` is true (default), terminal expansions are preferred so
    walks often finish with a literal or variable; PBT ADT sampling turns this
    off so recursive constructors are not starved by nullary ones.
    """
    partial = PartialAST(initial.term, list(initial.holes), initial.depth)
    for _ in range(max_depth * 2):
        if partial.is_complete():
            return partial.term

        completions = literal_completions(partial)
        if completions:
            return rng.choice(completions)

        hole = rng.choice(partial.holes)
        options = expansions_for_hole(partial, hole, skip, max_depth)
        if not options:
            return None
        if prefer_closed:
            closed = [opt for opt in options if not opt.holes]
            if closed:
                options = closed
        partial = rng.choice(options)

    return partial.term if partial.is_complete() else None


def initial_partial(ctx: TypingContext, target: Type) -> PartialAST:
    root, holes = peel_abstractions(target, ctx)
    return PartialAST(root, holes, depth=0)


def make_skip(fun_name: Name, metadata: Metadata) -> Callable[[Name], bool]:
    return make_skip_fn(fun_name, metadata)


def drive_candidates(
    candidates: Iterator[Term],
    validate: Callable[[Term], bool],
    evaluate: Callable[[Term], list[float]],
    fun_name: Name,
    metadata: Metadata,
    budget: float,
    ui: SynthesisUI,
    seed: int,
) -> Term | None:
    """Validate / evaluate yielded terms, keep a Pareto archive, pick one.

    With no objectives, returns the first candidate that typechecks. Otherwise
    runs until the wall-clock budget is exhausted (always assessing at least
    one candidate) and returns a seeded random member of the Pareto front.
    """
    goals: list[Goal] = metadata.get(fun_name, {}).get("goals", [])
    minimize = minimize_flags_from_goals(goals)
    started = monotonic()
    assessed = 0
    pareto_front: list[ParetoEntry] = []
    clear_tdsyn_caches()

    for candidate in candidates:
        assessed += 1
        valid = validate(candidate)

        if valid and not minimize:
            elapsed = monotonic() - started
            ui.register(candidate, [], elapsed, True)
            ui.progress(assessed, assessed, elapsed)
            return candidate

        score: list[float] | str = "Invalid"
        is_best = False
        if valid:
            try:
                values = evaluate(candidate)
            except (InvalidIndividualException, TimeoutInEvaluationException):
                pass
            else:
                if len(values) != len(minimize):
                    raise ValueError(f"Expected {len(minimize)} objective values, got {len(values)}")
                pareto_front, is_best = update_pareto_front(pareto_front, values, candidate, minimize)
                score = values

        elapsed = monotonic() - started
        ui.register(candidate, score, elapsed, is_best)
        ui.progress(assessed, assessed, elapsed)

        if elapsed >= max(0.0, budget):
            break

    if not pareto_front:
        return None
    return pick_pareto_member(pareto_front, seed)
