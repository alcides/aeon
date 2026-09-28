"""Shared Pareto archive helpers for synthesis backends.

All backends that optimise ``@minimize_*`` / ``@maximize_*`` (and related)
goals should use these helpers so dominance, mixed objective directions, and
front updates stay consistent.
"""

from __future__ import annotations

import random
from collections.abc import Sequence
from typing import TypeVar

from aeon.core.terms import Term
from aeon.synthesis.decorators import Goal

T = TypeVar("T")

ParetoEntry = tuple[list[float], Term]


def minimize_flags_from_goals(goals: Sequence[Goal]) -> list[bool]:
    """Expand decorator goals into a per-component minimize flag vector."""
    return [goal.minimize for goal in goals for _ in range(goal.length)]


def dominates(a: Sequence[float], b: Sequence[float], minimize: Sequence[bool]) -> bool:
    """Return whether ``a`` strictly Pareto-dominates ``b``."""
    if len(a) != len(b) or len(a) != len(minimize):
        raise ValueError("fitness vectors and objective directions must have equal lengths")
    no_worse = all(x <= y if is_min else x >= y for x, y, is_min in zip(a, b, minimize))
    strictly_better = any(x < y if is_min else x > y for x, y, is_min in zip(a, b, minimize))
    return no_worse and strictly_better


def update_pareto_front(
    front: list[tuple[list[float], T]],
    score: list[float],
    candidate: T,
    minimize: Sequence[bool],
) -> tuple[list[tuple[list[float], T]], bool]:
    """Insert an evaluated candidate and report whether it joins the front."""
    if any(dominates(existing_score, score, minimize) for existing_score, _ in front):
        return front, False
    remaining = [(old_score, old) for old_score, old in front if not dominates(score, old_score, minimize)]
    return remaining + [(score, candidate)], True


def pick_pareto_member(front: Sequence[tuple[list[float], T]], seed: int = 0) -> T:
    """Return one non-dominated candidate (seeded choice; unique if |front|=1)."""
    if not front:
        raise ValueError("cannot pick from an empty Pareto front")
    return random.Random(seed).choice(list(front))[1]
