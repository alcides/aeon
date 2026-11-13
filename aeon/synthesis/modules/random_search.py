"""Native random search over Aeon's core term grammar.

This backend has no GeneticEngine dependency.  Each sample is a random walk
that expands typed holes with Aeon's backward and forward grammar actions
until a complete term is produced (or the depth bound is hit);
:func:`~aeon.synthesis.modules.native_search.drive_candidates` validates,
evaluates, and maintains a Pareto archive.
"""

from __future__ import annotations

import random
from time import monotonic
from collections.abc import Callable, Iterator

from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.decorators.api import Metadata
from aeon.synthesis.joint import HoleSpec, JointCandidate, JointSynthesizer
from aeon.synthesis.modules.native_search import (
    MAX_DEPTH,
    drive_candidates,
    initial_partial,
    make_skip,
    sample_one,
)
from aeon.synthesis.qtt import QTTValidator
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
    *,
    deadline: float = float("inf"),
    check_sketch: Callable[[Term], bool] | None = None,
    max_attempts: int | None = None,
) -> Iterator[Term]:
    """Yield complete core terms by independent random walks over the grammar."""
    initial = initial_partial(ctx, target, check_sketch=check_sketch)
    if not initial.qtt_feasible():
        return
    skip = make_skip(fun_name, metadata)
    attempts = 0
    while monotonic() < deadline and (max_attempts is None or attempts < max_attempts):
        attempts += 1
        sample = sample_one(initial, skip, rng, max_depth)
        if sample is not None:
            yield sample


class RandomSearchSynthesizer(JointSynthesizer):
    """Driver over :func:`iter_random_candidates` with a live Pareto archive."""

    supports_size_objective = True

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
            iter_random_candidates(
                ctx,
                type,
                fun_name,
                metadata,
                rng,
                deadline=monotonic() + max(0.0, budget),
                check_sketch=validate.feasible if isinstance(validate, QTTValidator) else None,
            ),
            validate,
            evaluate,
            fun_name,
            metadata,
            budget,
            ui,
            self.seed,
            backend=self,
        )

    def synthesize_joint(
        self,
        holes: tuple[HoleSpec, ...],
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        fun_name: Name,
        metadata: Metadata,
        budget: float = 60,
        ui: SynthesisUI = SynthesisUI(),
    ) -> JointCandidate | None:
        rng = random.Random(self.seed)
        deadline = monotonic() + max(0.0, budget)
        initials = [initial_partial(h.ctx, h.type) for h in holes]

        def candidates() -> Iterator[Term]:
            first = True
            while first or monotonic() < deadline:
                first = False
                # Restart the entire product after a failed walk: retaining
                # previous siblings would lock search into their allocation.
                terms = [initial.term for initial in initials]
                for i, hole in enumerate(holes):
                    check_sketch = None
                    if isinstance(validate, QTTValidator):

                        def check_sketch(candidate: Term) -> bool:
                            product = tuple(candidate if j == i else term for j, term in enumerate(terms))
                            return validate.feasible(JointCandidate(product))

                    stream = iter_random_candidates(
                        hole.ctx,
                        hole.type,
                        hole.function,
                        metadata,
                        rng,
                        deadline=deadline,
                        check_sketch=check_sketch,
                        max_attempts=1,
                    )
                    term = next(stream, None)
                    if term is None:
                        break
                    terms[i] = term
                else:
                    yield JointCandidate(tuple(terms))

        result = drive_candidates(
            candidates(), validate, evaluate, fun_name, metadata, budget, ui, self.seed, backend=self
        )
        assert result is None or isinstance(result, JointCandidate)
        return result
