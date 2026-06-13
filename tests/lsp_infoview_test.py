"""Tests for the Lean-style info view: expression-at-cursor type, hole goals,
and the local/global context split backing the ``aeon/infoView`` request."""

from __future__ import annotations

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.lsp.infoview import compute_info_view, _hole_at
from aeon.lsp.typeindex import build_type_index
from aeon.synthesis.uis.api import SilentSynthesisUI


def analyse(src: str):
    """Parse ``src`` and return ``(driver, type_index, errors)``."""
    cfg = AeonConfig(synthesizer="gp", synthesis_ui=SilentSynthesisUI(), synthesis_budget=1)
    d = AeonDriver(cfg)
    errors = list(d.parse(filename="file:///t.ae", aeon_code=src))
    index = build_type_index(d.typing_ctx, d.core) if getattr(d, "core", None) is not None else None
    return d, index, errors


def info_at(src: str, line: int, character: int):
    d, index, _ = analyse(src)
    return compute_info_view(src, line, character, d.typing_ctx, index, getattr(d, "core", None))


def col_of(src: str, line0: int, needle: str) -> int:
    """0-indexed column of ``needle`` on (0-indexed) ``line0``."""
    return src.splitlines()[line0].index(needle)


SRC = "def inc (n:Int) : Int := n + 1;\ndef main (u:Int) : Int :=\n    let x := 41 in\n    inc x;\n"


# --------------------------------------------------------------------------- #
# Expression under the cursor
# --------------------------------------------------------------------------- #


def test_expression_type_at_literal():
    info = info_at(SRC, 2, col_of(SRC, 2, "41"))
    assert info.expression is not None
    assert "41" in info.expression.type
    assert info.expression.range[0] == 2  # 0-indexed line of the literal


def test_expression_none_outside_any_node():
    # Line 0 column 0 is the `def` keyword: no synthesized expression there.
    info = info_at(SRC, 0, 0)
    assert info.expression is None


# --------------------------------------------------------------------------- #
# Context: locals vs globals
# --------------------------------------------------------------------------- #


def test_locals_include_let_binding_and_parameter():
    info = info_at(SRC, 3, col_of(SRC, 3, "x"))
    local_names = [e.name for e in info.locals]
    assert "x" in local_names
    assert "u" in local_names


def test_globals_include_top_level_defs_but_not_locals():
    info = info_at(SRC, 3, col_of(SRC, 3, "x"))
    global_names = [e.name for e in info.globals]
    assert "inc" in global_names
    assert "main" in global_names
    assert "x" not in global_names


def test_local_types_are_refined():
    info = info_at(SRC, 3, col_of(SRC, 3, "x"))
    x = next(e for e in info.locals if e.name == "x")
    assert "41" in x.type  # singleton refinement from `let x := 41`


def test_inner_scope_not_leaked_to_outer_position():
    # In `inc`'s body only `n` is local; `x`/`u` belong to `main`.
    info = info_at(SRC, 0, col_of(SRC, 0, "n +"))
    local_names = [e.name for e in info.locals]
    assert "n" in local_names
    assert "x" not in local_names


# --------------------------------------------------------------------------- #
# Hole goals
# --------------------------------------------------------------------------- #

HOLE_SRC = "def main (u:Int) : Int :=\n    let x := 41 in\n    ?h;\n"


def test_hole_at_detects_cursor_on_hole():
    line = HOLE_SRC.splitlines()[2]
    c = line.index("?h")
    assert _hole_at(HOLE_SRC, 2, c) == "h"
    assert _hole_at(HOLE_SRC, 2, c + 2) == "h"  # just past the name still counts
    assert _hole_at(HOLE_SRC, 2, 0) is None


def test_goal_shown_for_hole():
    info = info_at(HOLE_SRC, 2, col_of(HOLE_SRC, 2, "?h") + 1)
    assert info.goal is not None
    assert info.goal.name == "h"
    assert "Int" in info.goal.type
    # The checker's polymorphic placeholder for the hole is suppressed.
    assert info.expression is None


def test_goal_context_includes_locals():
    info = info_at(HOLE_SRC, 2, col_of(HOLE_SRC, 2, "?h") + 1)
    local_names = [e.name for e in info.locals]
    assert "x" in local_names
    assert "u" in local_names


def test_no_goal_away_from_hole():
    info = info_at(HOLE_SRC, 1, col_of(HOLE_SRC, 1, "41"))
    assert info.goal is None


# --------------------------------------------------------------------------- #
# Robustness and serialisation
# --------------------------------------------------------------------------- #


def test_graceful_without_analysis_state():
    info = compute_info_view(SRC, 2, 5, None, None, None)
    assert info.expression is None and info.goal is None
    assert info.locals == [] and info.globals == []


def test_to_dict_is_json_serialisable():
    import json

    info = info_at(HOLE_SRC, 2, col_of(HOLE_SRC, 2, "?h") + 1)
    payload = info.to_dict()
    text = json.dumps(payload)
    assert '"goal"' in text
    assert payload["goal"]["name"] == "h"
    assert isinstance(payload["locals"], list)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
