"""Native random search over Aeon's core term grammar.

This backend has no GeneticEngine dependency.  Each sample is a random walk
that expands typed holes with Aeon's backward and forward grammar actions
until a complete term is produced (or the depth bound is hit);
:func:`~aeon.synthesis.modules.native_search.drive_candidates` validates,
evaluates, and maintains a Pareto archive.
"""

from __future__ import annotations

import random
from collections.abc import Callable, Iterator

from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer
from aeon.synthesis.modules.native_search import (
    MAX_DEPTH,
    drive_candidates,
    initial_partial,
    make_skip,
    sample_one,
)
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name

# Re-exported for unit tests that patch the walk helper by module attribute.
_sample_one = sample_one


def iter_random_candidates(
    ctx: TypingContext,
    target: Type,
    fun_name: Name,
    metadata: Metadata,
    rng: random.Random,
    max_depth: int = MAX_DEPTH,
) -> Iterator[Term]:
    """Yield complete core terms by independent random walks over the grammar."""
    initial = initial_partial(ctx, target)
    skip = make_skip(fun_name, metadata)
    while True:
        sample = sample_one(initial, skip, rng, max_depth)
        if sample is not None:
            yield sample


class RandomSearchSynthesizer(Synthesizer):
    """Driver over :func:`iter_random_candidates` with a live Pareto archive."""

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
        rng = random.Random(self.seed)
        return drive_candidates(
            iter_random_candidates(ctx, type, fun_name, metadata, rng),
            validate,
            evaluate,
            fun_name,
            metadata,
            budget,
            ui,
            self.seed,
        )
