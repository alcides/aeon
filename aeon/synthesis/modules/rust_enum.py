"""Rust-side random-enumerative synthesizer wrapper.

The actual term-generation loop, Pareto-front bookkeeping, and budget
management live in `aeon-rs/src/rust_enum_synth.rs`. This Python
wrapper subclasses :class:`Synthesizer` so the existing
:func:`make_synthesizer` factory and synthesis entry point treat it
uniformly with the other backends, but every call is forwarded
straight to the Rust object.

Algorithm sketch:
  1. Randomly generate a core Aeon term targeting the goal type
     (type-directed: emits literals for primitive targets, builds
     abstraction-chains for function-type targets, picks context
     variables whose return-type unifies with the target, builds
     application chains to fill in arguments).
  2. Type-check the term via the Python ``validate`` callback (which
     dispatches into the Rust type-checker). Reject failures.
  3. Evaluate the surviving term via the Python ``evaluate`` callback
     (runs the term in the Python evaluator + measures the user-defined
     fitness vector). Skip on exceptions or non-finite scores.
  4. Insert (score, term) into the Pareto front: anything the new
     candidate dominates is pruned; if nothing dominates it, it joins.
  5. Loop until the time budget expires; return the lex-smallest term
     from the final front.
"""

from __future__ import annotations

from typing import Callable

from aeon_rs import RustEnumSynthesizer as _RustEnumCore

from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer, SynthesisNotSuccessful
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


class RustEnumSynthesizerWrapper(Synthesizer):
    """Python-facing wrapper around the Rust core."""

    def __init__(self, seed: int = 42, max_depth: int = 5):
        self._core = _RustEnumCore(seed=seed, max_depth=max_depth)

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
        result = self._core.synthesize(
            ctx,
            type,
            validate,
            evaluate,
            fun_name,
            metadata,
            budget,
            ui,
        )
        if result is None:
            raise SynthesisNotSuccessful(
                "RustEnumSynthesizer: no valid candidate found within budget",
            )
        return result

    def synthesize_with_front(
        self,
        ctx: TypingContext,
        type: Type,
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        fun_name: Name,
        metadata: Metadata,
        budget: float = 60,
        ui: SynthesisUI | None = None,
    ) -> tuple[Term | None, list[tuple[list[float], Term]]]:
        """Like ``synthesize`` but also returns the full Pareto front."""
        return self._core.synthesize_with_front(
            ctx,
            type,
            validate,
            evaluate,
            fun_name,
            metadata,
            budget,
            ui,
        )
