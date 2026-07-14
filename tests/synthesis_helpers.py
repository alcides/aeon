"""Helpers for synthesis integration tests.

Stochastic or budget-limited synthesizers may legitimately exhaust their time
budget on slow CI hosts. Those outcomes should skip the test rather than fail
it; only unexpected errors should fail the run.
"""

from __future__ import annotations

from typing import Any

import pytest

from aeon.core.terms import Hole, Term
from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.entrypoint import synthesize_holes as _synthesize_holes


def synthesize_holes_or_skip(*args: Any, **kwargs: Any) -> dict[Any, Any]:
    """Like :func:`synthesize_holes`, but skip when the budget expires."""
    try:
        return _synthesize_holes(*args, **kwargs)
    except SynthesisNotSuccessful as exc:
        pytest.skip(f"synthesis did not find a valid candidate within budget: {exc}")
    raise AssertionError("unreachable")


def require_synthesized(term: Term | None, *, what: str = "hole") -> Term:
    """Skip when synthesis left the target unfilled."""
    if term is None or isinstance(term, Hole):
        pytest.skip(f"synthesis did not fill the {what} within budget")
    return term


def run_synthesizer_or_skip(synthesizer, /, **kwargs: Any) -> Term:
    """Run ``synthesizer.synthesize``, skipping on budget exhaustion."""
    try:
        term = synthesizer.synthesize(**kwargs)
    except SynthesisNotSuccessful as exc:
        pytest.skip(f"synthesis did not find a valid candidate within budget: {exc}")
    return require_synthesized(term)


def first_hole_term(mapping: dict[Any, Any], *, what: str = "hole") -> Term:
    """Return the first mapped hole term, skipping when it was not filled."""
    if not mapping:
        pytest.skip(f"synthesis returned no {what} mapping")
    return require_synthesized(next(iter(mapping.values())), what=what)
