"""Tests for the @skip_typecheck decorator + synthesize_holes wiring."""

from __future__ import annotations

from tests.driver import check_and_return_core


def _find_meta(metadata, key):
    for v in metadata.values():
        if isinstance(v, dict) and key in v:
            return v[key]
    return None


def test_skip_typecheck_sets_metadata_flag():
    source = r"""
        @skip_typecheck
        @csv_data("1.0,2.0\n3.0,4.0")
        def f (x:Float) : Float = ?hole
    """
    _, _, _, metadata = check_and_return_core(source)
    assert _find_meta(metadata, "skip_typecheck") is True


def test_skip_typecheck_does_not_strip_goals():
    """The flag is orthogonal to goal registration: @csv_data must still
    emit per-row goals when @skip_typecheck is present."""
    source = r"""
        @skip_typecheck
        @csv_data("1.0,2.0\n3.0,4.0\n5.0,6.0\n7.0,8.0")
        def f (x:Float) : Float = ?hole
    """
    _, _, _, metadata = check_and_return_core(source)
    goals = _find_meta(metadata, "goals")
    assert goals is not None and len(goals) == 4


def test_skip_typecheck_default_off():
    """Without the decorator, no flag is stamped — pipeline falls back
    to the real validator."""
    source = r"""
        @csv_data("1.0,2.0\n3.0,4.0")
        def f (x:Float) : Float = ?hole
    """
    _, _, _, metadata = check_and_return_core(source)
    # No `skip_typecheck` key set anywhere.
    for v in metadata.values():
        if isinstance(v, dict):
            assert "skip_typecheck" not in v


def test_skip_typecheck_combines_with_short_circuit():
    """Both flags can be set; they're independent metadata bits."""
    source = r"""
        @skip_typecheck
        @short_circuit
        @csv_data("1.0,2.0\n3.0,4.0")
        def f (x:Float) : Float = ?hole
    """
    _, _, _, metadata = check_and_return_core(source)
    assert _find_meta(metadata, "skip_typecheck") is True
    assert _find_meta(metadata, "short_circuit") is True
