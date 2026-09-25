"""Native breadth-first enumeration over Aeon's core term grammar.

This backend has no GeneticEngine dependency.  A generator expands typed holes
with Aeon's backward and forward grammar actions and yields each complete term;
a separate driver validates, evaluates, and maintains a Pareto archive.
"""

from __future__ import annotations

import random
from collections import deque
from collections.abc import Callable, Iterator, Sequence
from time import monotonic

from aeon.core.terms import Abstraction, Term
from aeon.core.types import AbstractionType, Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import InvalidIndividualException, Synthesizer, TimeoutInEvaluationException
from aeon.synthesis.decorators import Goal
from aeon.synthesis.modules.tdsyn.actions import backward_candidates, forward_candidates
from aeon.synthesis.modules.tdsyn.helpers import make_skip_fn
from aeon.synthesis.modules.tdsyn.smt_solve import all_leaf_holes, solve_literals
from aeon.synthesis.modules.tdsyn.worklist import PartialAST, TypedHole, fresh_hole, substitute_hole
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name

# Bound recursive expansions the same way as the type-directed BFS backend so
# that a single worklist pass cannot grow without bound before the budget ends.
MAX_DEPTH = 5

ParetoEntry = tuple[list[float], Term]

_loc = SynthesizedLocation("enumerative")


def _dominates(a: Sequence[float], b: Sequence[float], minimize: Sequence[bool]) -> bool:
    """Return whether ``a`` strictly Pareto-dominates ``b``."""
    if len(a) != len(b) or len(a) != len(minimize):
        raise ValueError("fitness vectors and objective directions must have equal lengths")
    no_worse = all(x <= y if is_min else x >= y for x, y, is_min in zip(a, b, minimize))
    strictly_better = any(x < y if is_min else x > y for x, y, is_min in zip(a, b, minimize))
    return no_worse and strictly_better


def _update_pareto_front(
    front: list[ParetoEntry],
    score: list[float],
    candidate: Term,
    minimize: Sequence[bool],
) -> tuple[list[ParetoEntry], bool]:
    """Insert an evaluated candidate and report whether it joins the front."""
    if any(_dominates(existing_score, score, minimize) for existing_score, _ in front):
        return front, False
    remaining = [(old_score, old) for old_score, old in front if not _dominates(score, old_score, minimize)]
    return remaining + [(score, candidate)], True


def _peel_abstractions(ty: Type, ctx: TypingContext) -> tuple[Term, list[TypedHole]]:
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


def _literal_completions(partial: PartialAST) -> list[Term]:
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


def iter_candidates(
    ctx: TypingContext,
    target: Type,
    fun_name: Name,
    metadata: Metadata,
    max_depth: int = MAX_DEPTH,
) -> Iterator[Term]:
    """Yield complete core terms breadth-first from Aeon's grammar actions.

    Backward actions cover variables, literals, applications, abstractions and
    conditionals. Forward actions additionally cover lets, applications,
    conditionals, type applications, abstractions and type abstractions.
    Refinement-constrained leaves are also completed from SMT models.
    """
    root, holes = _peel_abstractions(target, ctx)
    worklist: deque[PartialAST] = deque([PartialAST(root, holes, depth=0)])
    skip = make_skip_fn(fun_name, metadata)
    yielded: set[str] = set()

    def emit(term: Term) -> Iterator[Term]:
        key = str(term)
        if key not in yielded:
            yielded.add(key)
            yield term

    while worklist:
        partial = worklist.popleft()
        if partial.is_complete():
            yield from emit(partial.term)
            continue

        for term in _literal_completions(partial):
            yield from emit(term)

        hole = partial.holes[0]
        remaining = [other for other in partial.holes if other.name != hole.name]
        complete_next: list[PartialAST] = []
        incomplete_next: list[PartialAST] = []
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
                if depth > max_depth:
                    continue
                nxt = PartialAST(term, remaining + new_holes, depth)
                if new_holes:
                    incomplete_next.append(nxt)
                else:
                    complete_next.append(nxt)
        # Prefer terminals (literals / variables) before recursive expansions.
        worklist.extend(complete_next)
        worklist.extend(incomplete_next)


# Kept as an alias so existing unit tests can patch the generator by name.
_candidates = iter_candidates


class EnumerativeSynthesizer(Synthesizer):
    """Driver over :func:`iter_candidates` with a live Pareto archive."""

    def __init__(self, seed: int = 0):
        self.seed = seed

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
        assert isinstance(ctx, TypingContext)
        assert isinstance(type, Type)

        goals: list[Goal] = metadata.get(fun_name, {}).get("goals", [])
        minimize = [goal.minimize for goal in goals for _ in range(goal.length)]
        started = monotonic()
        assessed = 0
        pareto_front: list[ParetoEntry] = []

        for candidate in iter_candidates(ctx, type, fun_name, metadata):
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
                    pareto_front, is_best = _update_pareto_front(pareto_front, values, candidate, minimize)
                    score = values

            elapsed = monotonic() - started
            ui.register(candidate, score, elapsed, is_best)
            ui.progress(assessed, assessed, elapsed)

            # Assess at least one candidate (historical zero-budget behaviour),
            # then stop once the wall-clock budget is exhausted.
            if elapsed >= max(0.0, budget):
                break

        if not pareto_front:
            return None
        return random.Random(self.seed).choice(pareto_front)[1]
