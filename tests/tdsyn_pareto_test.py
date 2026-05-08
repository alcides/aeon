"""Tests for tdsyn's Pareto-front + ε-dominance helpers."""

from __future__ import annotations

from aeon.core.terms import Literal
from aeon.core.types import t_int
from aeon.synthesis.modules.tdsyn.synthesizer import (
    _eps_dominates,
    _front_offer,
    _select_from_front,
)


def _t(n: int) -> Literal:
    """Convenience: a unique Term per integer."""
    return Literal(n, t_int)


def test_eps_dominates_strict_zero_eps():
    # [1, 2] strictly dominates [2, 3] with eps=0.
    assert _eps_dominates([1.0, 2.0], [2.0, 3.0], 0.0)
    # Equal vectors don't dominate.
    assert not _eps_dominates([1.0, 2.0], [1.0, 2.0], 0.0)
    # Mixed: better on one, worse on another => no domination.
    assert not _eps_dominates([1.0, 5.0], [2.0, 4.0], 0.0)


def test_eps_dominates_with_epsilon():
    # With eps=0.1, [1.0, 2.0] does NOT strictly dominate [1.05, 2.05]
    # (the difference of 0.05 on each axis is within ε, so no axis is
    # "more than ε better").
    assert not _eps_dominates([1.0, 2.0], [1.05, 2.05], 0.1)
    # But it does at eps=0.01 (each axis is ≥0.04 better, beyond ε).
    assert _eps_dominates([1.0, 2.0], [1.05, 2.05], 0.01)


def test_front_offer_keeps_dominators():
    front = []
    assert _front_offer(front, [10.0, 10.0], _t(1), 0.0)
    # Worse on every axis: rejected.
    assert not _front_offer(front, [11.0, 11.0], _t(2), 0.0)
    assert len(front) == 1


def test_front_offer_evicts_dominated():
    front = []
    _front_offer(front, [10.0, 10.0], _t(1), 0.0)
    # [5, 5] dominates [10, 10] => evict the old, keep new.
    assert _front_offer(front, [5.0, 5.0], _t(2), 0.0)
    assert len(front) == 1
    assert front[0][1] == _t(2)


def test_front_offer_keeps_incomparable():
    """Specialists on different axes both stay on the front."""
    front = []
    _front_offer(front, [1.0, 10.0], _t(1), 0.0)
    _front_offer(front, [10.0, 1.0], _t(2), 0.0)
    _front_offer(front, [5.0, 5.0], _t(3), 0.0)
    assert len(front) == 3


def test_eps_filter_collapses_near_duplicates():
    front = []
    _front_offer(front, [1.0, 2.0], _t(1), eps=0.1)
    # Within eps on every axis: rejected as a near-duplicate of point #1.
    assert not _front_offer(front, [1.05, 2.05], _t(2), eps=0.1)
    assert len(front) == 1


def test_eps_filter_admits_distant_neighbour():
    front = []
    _front_offer(front, [1.0, 2.0], _t(1), eps=0.1)
    # Trade-off candidate: better on axis 1, worse on axis 2, beyond eps.
    assert _front_offer(front, [0.5, 3.0], _t(2), eps=0.1)
    assert len(front) == 2


def test_select_from_front_picks_min_sum():
    front = [
        ([1.0, 10.0], _t(1)),    # sum=11
        ([10.0, 1.0], _t(2)),    # sum=11
        ([5.0, 5.0], _t(3)),     # sum=10  ← chosen
    ]
    chosen = _select_from_front(front)
    assert chosen == _t(3)


def test_select_from_front_empty_returns_none():
    assert _select_from_front([]) is None
