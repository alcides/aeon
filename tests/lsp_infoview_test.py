"""Tests for the Lean-style info view: the turnstile target (expression type /
hole goal), the local/global context split, the base/predicate rendering and the
hiding of anonymous binders backing the ``aeon/infoView`` request."""

from __future__ import annotations

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.lsp.infoview import (
    _hole_at,
    _is_hidden,
    _pp_liquid,
    _pp_refinement,
    _pp_type,
    _strip_ids,
    compute_info_view,
)
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
# Pretty printing never shows internal name ids
# --------------------------------------------------------------------------- #

# Internal name ids render as superscript digits (``v⁴⁴⁸``, ``p⁷²``).
SUPERSCRIPT_DIGITS = "⁰¹²³⁴⁵⁶⁷⁸⁹"


def _has_id(s) -> bool:
    return s is not None and any(ch in SUPERSCRIPT_DIGITS for ch in s)


def test_strip_ids_removes_superscript_digits():
    assert _strip_ids("v⁴⁴⁸") == "v"
    assert _strip_ids("p⁷²(ν)") == "p(ν)"
    assert _strip_ids("Int") == "Int"


def test_pp_type_strips_ids_of_terms():
    from aeon.core.liquid import LiquidApp, LiquidVar
    from aeon.core.types import RefinedType, t_int
    from aeon.utils.name import Name

    # A refinement whose bound and free variables carry non-zero ids.
    k = Name("k", 7)
    x = Name("x", 12)
    ref = LiquidApp(Name(">", 0), [LiquidVar(k), LiquidVar(x)])
    ty = RefinedType(k, t_int, ref)
    rendered = _pp_type(ty)
    assert not _has_id(rendered), rendered
    # the free variable keeps its surface name, without the id
    assert "x" in rendered and "x¹²" not in rendered


def test_pp_liquid_uses_surface_names_without_ids():
    from aeon.core.liquid import LiquidApp, LiquidVar
    from aeon.utils.name import Name

    expr = LiquidApp(Name(">", 0), [LiquidVar(Name("v", 448)), LiquidVar(Name("y", 3))])
    assert _pp_liquid(expr) == "v > y"


def test_no_ids_anywhere_in_context_or_target():
    # The prelude binds polymorphic operators (e.g. `$`) whose types carry
    # horn-application ids like `p⁷²(ν)`; none must reach the rendered output.
    info = info_at(SRC, 3, col_of(SRC, 3, "x"))
    for e in info.locals + info.globals:
        assert not _has_id(e.name), e.name
        assert not _has_id(e.type), (e.name, e.type)
        assert not _has_id(e.predicate), (e.name, e.predicate)
    if info.target is not None:
        assert not _has_id(info.target.type)
        assert not _has_id(info.target.predicate)


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


def test_function_application_has_space_before_args():
    from aeon.core.liquid import LiquidApp, LiquidVar
    from aeon.utils.name import Name

    def v(n):
        return LiquidVar(Name(n, 0))

    # `f(a && b)` reads as `f (a && b)`.
    expr = LiquidApp(Name("f", 0), [LiquidApp(Name("&&", 0), [v("a"), v("b")])])
    assert _pp_liquid(expr) == "f (a && b)"


# --------------------------------------------------------------------------- #
# Refinements are presented in CNF (a list of conditions)
# --------------------------------------------------------------------------- #


def _v(n):
    from aeon.core.liquid import LiquidVar
    from aeon.utils.name import Name

    return LiquidVar(Name(n, 0))


def _app(op, *args):
    from aeon.core.liquid import LiquidApp
    from aeon.utils.name import Name

    return LiquidApp(Name(op, 0), list(args))


def test_cnf_distributes_or_over_and():
    # a || (b && c)  ->  (a || b) && (a || c)
    expr = _app("||", _v("a"), _app("&&", _v("b"), _v("c")))
    assert _pp_refinement(expr) == "(a || b) && (a || c)"


def test_cnf_eliminates_implication():
    # a --> b  ->  !a || b  (single condition, so no surrounding parens)
    assert _pp_refinement(_app("-->", _v("a"), _v("b"))) == "!a || b"


def test_cnf_pushes_negation_inwards():
    # !(a && b)  ->  !a || !b
    assert _pp_refinement(_app("!", _app("&&", _v("a"), _v("b")))) == "!a || !b"


def test_cnf_keeps_conjunction_as_condition_list():
    from aeon.core.liquid import LiquidLiteralInt

    expr = _app("&&", _app(">", _v("x"), LiquidLiteralInt(0)), _app("<", _v("x"), LiquidLiteralInt(10)))
    assert _pp_refinement(expr) == "x > 0 && x < 10"


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
