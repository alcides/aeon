"""Opt-in verification evidence, scoped to one analysis (not global LSP state)."""

from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, replace
from typing import Iterator, Literal

from aeon.verification.vcs import (
    Constraint,
    Conjunction,
    Implication,
    ReflectedFunctionDeclaration,
    UninterpretedFunctionDeclaration,
)
from aeon.utils.location import Location

Status = Literal["valid", "invalid", "unknown", "unsupported"]


@dataclass(frozen=True)
class VerificationResult:
    constraint: Constraint
    status: Status
    reason: str | None = None
    cached: bool = False


_collector: ContextVar[list[VerificationResult] | None] = ContextVar("verification_collector", default=None)


@contextmanager
def collect_verification() -> Iterator[list[VerificationResult]]:
    results: list[VerificationResult] = []
    token = _collector.set(results)
    try:
        yield results
    finally:
        _collector.reset(token)


def record_verification(result: VerificationResult) -> None:
    collector = _collector.get()
    if collector is not None:
        collector.append(result)


@contextmanager
def suspend_verification() -> Iterator[None]:
    """Hide exploratory qualifier queries, which are not program obligations."""
    token = _collector.set(None)
    try:
        yield
    finally:
        _collector.reset(token)


def conjuncts(constraint: Constraint) -> Iterator[Constraint]:
    """Split goals while retaining their assumptions, declarations and spans.

    A valid conjunction proves every conjunct. For failed conjunctions callers
    must retain the aggregate status; failure does not disprove every goal.
    """
    if isinstance(constraint, Conjunction):
        yield from conjuncts(constraint.c1)
        yield from conjuncts(constraint.c2)
    elif isinstance(constraint, (Implication, ReflectedFunctionDeclaration, UninterpretedFunctionDeclaration)):
        for goal in conjuncts(constraint.seq):
            yield replace(constraint, seq=goal)
    else:
        yield constraint


def goal_location(constraint: Constraint) -> Location | None:
    """Prefer the goal's span over locations on imported context binders."""
    if isinstance(constraint, (Implication, ReflectedFunctionDeclaration, UninterpretedFunctionDeclaration)):
        return goal_location(constraint.seq) or getattr(constraint, "loc", None)
    if isinstance(constraint, Conjunction):
        return goal_location(constraint.c1) or goal_location(constraint.c2)
    return getattr(constraint, "loc", None)
