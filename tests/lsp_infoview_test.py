"""Tests for the Lean-style info view: the turnstile target (expression type /
hole goal), the local/global context split, the base/predicate rendering and the
hiding of anonymous binders backing the ``aeon/infoView`` request."""

from __future__ import annotations

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.lsp.infoview import _hole_at, _is_hidden, _pp_liquid, compute_info_view
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
# Turnstile target (expression type / hole goal)
# --------------------------------------------------------------------------- #


def test_target_type_at_literal():
    info = info_at(SRC, 2, col_of(SRC, 2, "41"))
    assert info.target is not None
    # The literal's singleton type ``{ν:Int | ν == 41}`` splits into base + pred.
    assert info.target.type == "Int"
    assert info.target.predicate is not None and "41" in info.target.predicate


def test_target_none_outside_any_node():
    # Line 0 column 0 is the `def` keyword: no synthesized expression there.
    info = info_at(SRC, 0, 0)
    assert info.target is None


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


def test_globals_include_operators_and_builtins():
    # "All variables in context": operators (non-identifier binders like `+`)
    # and the rest of the prelude are reported in the globals section.
    info = info_at(SRC, 3, col_of(SRC, 3, "x"))
    global_names = {e.name for e in info.globals}
    assert "+" in global_names
    assert "==" in global_names


def test_local_types_are_refined_with_outer_name():
    info = info_at(SRC, 3, col_of(SRC, 3, "x"))
    x = next(e for e in info.locals if e.name == "x")
    assert x.type == "Int"
    # singleton refinement from `let x := 41`, renamed to the outer name `x`.
    assert x.predicate is not None
    assert "x" in x.predicate and "41" in x.predicate


def test_inner_scope_not_leaked_to_outer_position():
    # In `inc`'s body only `n` is local; `x`/`u` belong to `main`.
    info = info_at(SRC, 0, col_of(SRC, 0, "n +"))
    local_names = [e.name for e in info.locals]
    assert "n" in local_names
    assert "x" not in local_names


# --------------------------------------------------------------------------- #
# Refinement rendering: outer name, pretty predicate, anonymous hiding
# --------------------------------------------------------------------------- #

REFINED_SRC = "def f (x:{k:Int | k > 0 && k < 10}) : Int := x + 0;\n"


def test_refinement_uses_outer_name_and_pretty_print():
    # `x:{k:Int | k > 0 && k < 10}` is shown as `x : Int` | `x > 0 && x < 10`:
    # bound variable renamed to the outer name, no redundant parentheses.
    info = info_at(REFINED_SRC, 0, col_of(REFINED_SRC, 0, "x + 0"))
    x = next(e for e in info.locals if e.name == "x")
    assert x.type == "Int"
    assert x.predicate == "x > 0 && x < 10"


def test_anonymous_binders_are_hidden():
    assert _is_hidden("_")
    assert _is_hidden("_cond")
    assert _is_hidden("_inner_x")
    assert not _is_hidden("x")
    assert not _is_hidden("+")
    # No context entry is ever anonymous.
    info = info_at(REFINED_SRC, 0, col_of(REFINED_SRC, 0, "x + 0"))
    assert all(not e.name.startswith("_") for e in info.locals + info.globals)


# --------------------------------------------------------------------------- #
# Predicate pretty-printer
# --------------------------------------------------------------------------- #


def test_pp_liquid_minimal_parens():
    from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
    from aeon.utils.name import Name

    def app(op, a, b):
        return LiquidApp(Name(op, 0), [a, b])

    x = LiquidVar(Name("x", 0))
    zero = LiquidLiteralInt(0)
    ten = LiquidLiteralInt(10)
    # (x > 0) && (x < 10) -> comparisons bind tighter than &&, so no parens.
    expr = app("&&", app(">", x, zero), app("<", x, ten))
    assert _pp_liquid(expr) == "x > 0 && x < 10"


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


def test_goal_target_shown_for_hole():
    info = info_at(HOLE_SRC, 2, col_of(HOLE_SRC, 2, "?h") + 1)
    assert info.target is not None
    assert "Int" in info.target.type


def test_goal_context_includes_locals():
    info = info_at(HOLE_SRC, 2, col_of(HOLE_SRC, 2, "?h") + 1)
    local_names = [e.name for e in info.locals]
    assert "x" in local_names
    assert "u" in local_names


# --------------------------------------------------------------------------- #
# Robustness and serialisation
# --------------------------------------------------------------------------- #


def test_graceful_without_analysis_state():
    info = compute_info_view(SRC, 2, 5, None, None, None)
    assert info.target is None
    assert info.locals == [] and info.globals == []


def test_to_dict_is_json_serialisable():
    import json

    info = info_at(REFINED_SRC, 0, col_of(REFINED_SRC, 0, "x + 0"))
    payload = info.to_dict()
    text = json.dumps(payload)
    assert '"target"' in text
    assert isinstance(payload["locals"], list)
    x = next(e for e in payload["locals"] if e["name"] == "x")
    assert x["type"] == "Int"
    assert x["predicate"] == "x > 0 && x < 10"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
