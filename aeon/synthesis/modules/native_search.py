"""Shared helpers for native grammar-search backends (no GeneticEngine).

Both :mod:`enumerative` and :mod:`random_search` expand Aeon's core term
grammar via the type-directed backward/forward actions and drive candidates
through the same validate / evaluate / Pareto archive loop.
"""

from __future__ import annotations

import random
from collections.abc import Callable, Iterator, Sequence
from time import monotonic

from aeon.core.terms import Abstraction, Term
from aeon.core.types import AbstractionType, Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import InvalidIndividualException, TimeoutInEvaluationException
from aeon.synthesis.decorators import Goal
from aeon.synthesis.modules.tdsyn.actions import backward_candidates, forward_candidates
from aeon.synthesis.modules.tdsyn.helpers import make_skip_fn
from aeon.synthesis.modules.tdsyn.smt_solve import all_leaf_holes, solve_literals
from aeon.synthesis.modules.tdsyn.worklist import PartialAST, TypedHole, fresh_hole, substitute_hole
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name

# Bound recursive expansions so a single sample / worklist pass cannot grow
# without bound before the wall-clock budget ends.
MAX_DEPTH = 5

ParetoEntry = tuple[list[float], Term]

_loc = SynthesizedLocation("native_search")


def dominates(a: Sequence[float], b: Sequence[float], minimize: Sequence[bool]) -> bool:
    """Return whether ``a`` strictly Pareto-dominates ``b``."""
    if len(a) != len(b) or len(a) != len(minimize):
        raise ValueError("fitness vectors and objective directions must have equal lengths")
    no_worse = all(x <= y if is_min else x >= y for x, y, is_min in zip(a, b, minimize))
    strictly_better = any(x < y if is_min else x > y for x, y, is_min in zip(a, b, minimize))
    return no_worse and strictly_better


def update_pareto_front(
    front: list[ParetoEntry],
    score: list[float],
    candidate: Term,
    minimize: Sequence[bool],
) -> tuple[list[ParetoEntry], bool]:
    """Insert an evaluated candidate and report whether it joins the front."""
    if any(dominates(existing_score, score, minimize) for existing_score, _ in front):
        return front, False
    remaining = [(old_score, old) for old_score, old in front if not dominates(score, old_score, minimize)]
    return remaining + [(score, candidate)], True


def peel_abstractions(ty: Type, ctx: TypingContext) -> tuple[Term, list[TypedHole]]:
    """Wrap a function goal as ``λ…λ.?hole`` and extend the context with binders."""
    if not isinstance(ty, AbstractionType):
        hole_term, typed_hole = fresh_hole(ty, ctx)
        return hole_term, [typed_hole]

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
    return term, [inner_typed_hole]


def literal_completions(partial: PartialAST) -> list[Term]:
    """Complete a leaf-only partial term with each model supplied by Z3."""
    if not partial.holes or not all_leaf_holes(partial.holes):
        return []
    completed: list[Term] = []
    for solution in solve_literals(partial.holes):
        term = partial.term
        for hole_name, literal in solution.items():
            term = substitute_hole(term, hole_name, literal)
        completed.append(term)
    return completed


def expansions_for_hole(
    partial: PartialAST,
    hole: TypedHole,
    skip: Callable[[Name], bool],
    max_depth: int,
) -> list[PartialAST]:
    """Apply every grammar action to ``hole`` and return depth-bounded partials."""
    remaining = [other for other in partial.holes if other.name != hole.name]
    results: list[PartialAST] = []
    for action in (backward_candidates, forward_candidates):
        try:
            expansions = action(hole, skip)
        except Exception:
            # An action can be inapplicable to a particular dependent type;
            # the other grammar productions must remain available.
            continue
        for replacement, new_holes in expansions:
            term = substitute_hole(partial.term, hole.name, replacement)
            depth = partial.depth + (1 if new_holes else 0)
            if depth <= max_depth:
                results.append(PartialAST(term, remaining + new_holes, depth))
    return results


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
    minimize = [goal.minimize for goal in goals for _ in range(goal.length)]
    started = monotonic()
    assessed = 0
    pareto_front: list[ParetoEntry] = []

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
    return random.Random(seed).choice(pareto_front)[1]
