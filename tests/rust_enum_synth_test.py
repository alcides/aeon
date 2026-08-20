"""Tests for the Rust-based random-enumerative synthesizer with Pareto front.

Both Rust entry points (``synthesize`` and ``synthesize_with_front``)
duck-type the typing context — any object with a ``vars()`` method works —
so they accept the pipeline's :class:`aeon.typechecking.context.TypingContext`
directly.
"""

from __future__ import annotations


from aeon_rs import RustEnumSynthesizer
from aeon.synthesis.modules.rust_enum import RustEnumSynthesizerWrapper
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.typechecking.context import TypingContext, VariableBinder
from aeon.core.types import t_int
from aeon.utils.name import Name


def test_construct() -> None:
    s = RustEnumSynthesizer(seed=42, max_depth=3)
    assert s is not None


def test_factory_returns_wrapper() -> None:
    s = make_synthesizer("rust_enum")
    assert isinstance(s, RustEnumSynthesizerWrapper)


def test_minimal_int_target() -> None:
    """With a trivially-accepting validator and constant fitness, the
    synthesizer should produce at least one candidate in the Pareto front."""
    ctx = TypingContext([VariableBinder(Name("x", 1), t_int)])

    def validate(_t):
        return True

    def evaluate(_t):
        return [0.0]

    s = RustEnumSynthesizer(seed=42, max_depth=2)
    best, front = s.synthesize_with_front(
        ctx,
        t_int,
        validate,
        evaluate,
        Name("dummy", 0),
        {},
        0.5,
        None,
    )
    assert best is not None
    assert len(front) >= 1


def test_pareto_keeps_non_dominated() -> None:
    """When fitness has two components and they trade off, the Pareto
    front should accumulate multiple non-dominated points."""
    ctx = TypingContext([VariableBinder(Name("x", 1), t_int)])

    seen = []

    def validate(_t):
        return True

    counter = [0]

    def evaluate(_t):
        counter[0] += 1
        # Two-objective: alternate trade-offs.
        a = counter[0] % 5
        b = 4 - a
        seen.append((a, b))
        return [float(a), float(b)]

    s = RustEnumSynthesizer(seed=7, max_depth=1)
    best, front = s.synthesize_with_front(
        ctx,
        t_int,
        validate,
        evaluate,
        Name("d", 0),
        {},
        0.5,
        None,
    )
    # Across the 5 trade-off points (0,4), (1,3), (2,2), (3,1), (4,0),
    # all are mutually non-dominated.  With enough iterations the front
    # should contain them all.
    assert best is not None
    # The front should hold multiple distinct points.
    distinct_scores = {tuple(score) for score, _ in front}
    assert len(distinct_scores) >= 2, f"got only {distinct_scores}"


def test_rejects_invalid_terms() -> None:
    """The validator rejects every candidate; result should be None."""
    ctx = TypingContext([VariableBinder(Name("x", 1), t_int)])

    def validate(_t):
        return False

    def evaluate(_t):
        return [0.0]

    s = RustEnumSynthesizer(seed=42, max_depth=2)
    best, front = s.synthesize_with_front(
        ctx,
        t_int,
        validate,
        evaluate,
        Name("d", 0),
        {},
        0.2,
        None,
    )
    assert best is None
    assert len(front) == 0
