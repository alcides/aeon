"""Native breadth-first enumeration over Aeon's core term grammar.

This backend has no GeneticEngine dependency.  A generator expands typed holes
with Aeon's backward and forward grammar actions and yields each complete term;
:func:`~aeon.synthesis.modules.native_search.drive_candidates` validates,
evaluates, and maintains a Pareto archive.
"""

from __future__ import annotations

from collections import deque
from collections.abc import Callable, Iterator
from time import monotonic

from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer
from aeon.synthesis.modules.native_search import (
    MAX_DEPTH,
    drive_candidates,
    expansions_for_hole,
    initial_partial,
    literal_completions,
    make_skip,
)
from aeon.synthesis.modules.tdsyn.worklist import PartialAST
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def iter_candidates(
    ctx: TypingContext,
    target: Type,
    fun_name: Name,
    metadata: Metadata,
    max_depth: int = MAX_DEPTH,
    *,
    budget: float | None = None,
    skip: Callable[[Name], bool] | None = None,
    max_expansions: int | None = None,
    max_worklist: int | None = None,
) -> Iterator[Term]:
    """Yield complete core terms breadth-first from Aeon's grammar actions.

    Backward actions cover variables, literals, applications, abstractions and
    conditionals. Forward actions cover applications grown from in-scope
    variables. Refinement-constrained leaves are also completed from SMT models.
    """
    worklist: deque[PartialAST] = deque([initial_partial(ctx, target)])
    skip = make_skip(fun_name, metadata) if skip is None else skip
    yielded: set[Term] = set()
    deadline = None if budget is None else monotonic() + max(0.0, budget)

    def emit(term: Term) -> Iterator[Term]:
        if term not in yielded:
            yielded.add(term)
            yield term

    expanded = 0
    while worklist:
        # A long stretch of partial trees may yield no candidate at all. The
        # consumer cannot enforce its budget until next() returns, so enforce
        # it here too. Still permit the first candidate for a zero budget.
        if deadline is not None and (yielded or (budget is not None and budget > 0)) and monotonic() >= deadline:
            return
        partial = worklist.popleft()
        if partial.is_complete():
            yield from emit(partial.term)
            continue

        for term in literal_completions(partial):
            yield from emit(term)

        if max_expansions is not None and expanded >= max_expansions:
            return
        expanded += 1

        hole = partial.holes[0]
        complete_next: list[PartialAST] = []
        incomplete_next: list[PartialAST] = []
        for nxt in expansions_for_hole(partial, hole, skip, max_depth):
            if nxt.holes:
                incomplete_next.append(nxt)
            else:
                complete_next.append(nxt)
        # Prefer terminals (literals / variables) before recursive expansions.
        worklist.extend(complete_next)
        worklist.extend(incomplete_next)
        if max_worklist is not None and len(worklist) > max_worklist:
            return


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
        return drive_candidates(
            iter_candidates(ctx, type, fun_name, metadata, budget=budget),
            validate,
            evaluate,
            fun_name,
            metadata,
            budget,
            ui,
            self.seed,
        )
