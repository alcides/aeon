"""Tests for the @short_circuit decorator + make_evaluator integration."""

from __future__ import annotations

from aeon.synthesis.entrypoint import make_evaluator
from aeon.backend.evaluator import EvaluationContext

from tests.driver import check_and_return_core


def _find_meta(metadata, key):
    for v in metadata.values():
        if isinstance(v, dict) and key in v:
            return v[key]
    return None


def test_short_circuit_decorator_sets_metadata_flag():
    source = r"""
        @short_circuit
        @csv_data("1.0,2.0\n3.0,4.0")
        def f (x:Float) : Float = ?hole
    """
    _, _, _, metadata = check_and_return_core(source)
    assert _find_meta(metadata, "short_circuit") is True


def test_short_circuit_keeps_per_row_goals():
    """The @short_circuit flag changes how goals are scored, not how many
    are registered — @csv_data still emits one Goal per row so the
    iteration order is well-defined."""
    source = r"""
        @short_circuit
        @csv_data("1.0,2.0\n3.0,4.0\n5.0,6.0")
        def f (x:Float) : Float = ?hole
    """
    _, _, _, metadata = check_and_return_core(source)
    goals = _find_meta(metadata, "goals")
    assert goals is not None and len(goals) == 3


def _stub_evaluator_returning(*scores):
    """Helper: build a list of stub evaluators, each returning a fixed score."""
    return [(lambda s=s: (lambda _term: s))() for s in scores]


def test_make_evaluator_short_circuit_perfect_score():
    """All goals pass (0.0) — wrapper returns [0.0]."""
    evs = _stub_evaluator_returning(0.0, 0.0, 0.0, 0.0)
    evaluate = make_evaluator(EvaluationContext(), lambda x: x, evs, short_circuit=True)
    assert evaluate(None) == [0.0]


def test_make_evaluator_short_circuit_first_failure():
    """Row 0 passes, row 1 fails — wrapper returns [3.0] (3 unpassed of 4)."""
    evs = _stub_evaluator_returning(0.0, 4.0, 9.0, 0.0)
    evaluate = make_evaluator(EvaluationContext(), lambda x: x, evs, short_circuit=True)
    assert evaluate(None) == [3.0]


def test_make_evaluator_short_circuit_all_fail():
    """Even row 0 fails — worst possible score."""
    evs = _stub_evaluator_returning(7.0, 0.0, 0.0, 0.0)
    evaluate = make_evaluator(EvaluationContext(), lambda x: x, evs, short_circuit=True)
    assert evaluate(None) == [4.0]


def test_make_evaluator_short_circuit_handles_exceptions():
    """An exception inside an evaluator counts as a failure for that row."""
    def boom(_):
        raise ValueError("oops")

    def ok(_):
        return 0.0

    evaluate = make_evaluator(EvaluationContext(), lambda x: x, [ok, boom, ok], short_circuit=True)
    # Row 0 passes, row 1 throws => stop, 2 unpassed of 3.
    assert evaluate(None) == [2.0]


def test_make_evaluator_default_mode_returns_full_vector():
    """Without short_circuit, behaviour is unchanged: return every score."""
    evs = _stub_evaluator_returning(0.0, 4.0, 9.0)
    evaluate = make_evaluator(EvaluationContext(), lambda x: x, evs, short_circuit=False)
    assert evaluate(None) == [0.0, 4.0, 9.0]
