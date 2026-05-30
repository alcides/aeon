"""Unit tests for the Vericoding Dafny-to-Aeon translator.

Tests the translator in isolation (no aeon compilation, no network). The
end-to-end harness lives at benchmarks/vericoding/run.py and is exercised
manually / by CI via a small smoke test.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "benchmarks" / "vericoding"))
from translate import (  # noqa: E402
    TranslationError,
    _expand_chained_comparison,
    _expand_implication,
    _expand_iff,
    _expand_var_bindings,
    _rewrite_calls,
    _wrap_negative_literals,
    translate,
    translate_expression,
)


def test_implication_at_top_level():
    # `==>` maps to aeon's `-->`, now registered in the prelude.
    assert _expand_implication("a ==> b") == "((a) --> (b))"


def test_implication_inside_parens():
    # Implication expansion must descend into parens, otherwise nested
    # implications survive into the aeon output where `==>` is a parse error.
    out = _expand_implication("(x ==> y)")
    assert "==>" not in out
    assert "-->" in out


def test_iff_becomes_equality():
    assert _expand_iff("a <==> b") == "(a) == (b)"


def test_chained_comparison_pairwise():
    assert _expand_chained_comparison("1 <= n <= 100") == "(1 <= n) && (n <= 100)"


def test_chained_comparison_with_and_split():
    # Each conjunct must be parenthesised separately so that aeon's
    # right-associative `==`/`&&` don't reassociate `a == 1 && b == 2`
    # into `a == (1 && (b == 2))`.
    out = _expand_chained_comparison("a == 1 && b == 2")
    assert out == "(a == 1) && (b == 2)"


def test_chained_comparison_does_not_split_implication():
    # The `>` in `==>` (and in the emitted `-->`) must not be treated as a
    # comparison operator.
    out = translate_expression("k == 1 ==> b >= a")
    assert "==>" not in out
    assert "(k == 1) --> (b >= a)" in out


def test_var_bindings_become_let_with_scope_parens():
    # Without explicit parens around REST, downstream chain-expansion would
    # split through the `&&` and lose the let scope.
    out = _expand_var_bindings("var x := 1; var y := 2; x + y > 0")
    assert out == "let x = 1 in let y = 2 in (x + y > 0)"


def test_calls_become_curried():
    assert _rewrite_calls("f(a, b, c)") == "(f a b c)"


def test_keyword_in_is_not_a_call():
    # `let x = 1 in (...)` — `in` is a keyword, not a function. The translator
    # must not rewrite it as `(in ...)`.
    out = _rewrite_calls("let x = 1 in (x + 1)")
    assert "(in" not in out


def test_negative_literal_after_comparison():
    # Aeon's grammar doesn't accept leading `-` where `expression_bool` is
    # expected, so `result >= -1` must become `result >= (0 - 1)`.
    out = _wrap_negative_literals("result >= -1")
    assert "(0 - 1)" in out


def test_negative_identifier_after_implication():
    # `-x` is also unary minus, e.g. in `... || -x == y`.
    out = _wrap_negative_literals("(!(x < 0)) || -x == y")
    assert "(0 - x)" in out


def test_rejects_blocker_features():
    bad = """
// <vc-preamble>
predicate P(s: seq<int>) { |s| > 0 }
// </vc-preamble>
// <vc-spec>
method M() returns (r: int)
// </vc-spec>
// <vc-code>
{ assume {:axiom} false; }
// </vc-code>
"""
    with pytest.raises(TranslationError, match="blocker"):
        translate(bad, "TEST")


def test_rejects_undefined_reference():
    # Spec calls `NoSuch(x)` but there's no predicate named `NoSuch`.
    bad = """
// <vc-preamble>
// </vc-preamble>
// <vc-spec>
method M(x: int) returns (r: int)
  ensures NoSuch(x, r)
// </vc-spec>
// <vc-code>
{ assume {:axiom} false; }
// </vc-code>
"""
    with pytest.raises(TranslationError, match="undefined"):
        translate(bad, "TEST")


def test_translates_simple_abs():
    """End-to-end translator pass on the canonical `Abs` task (DD0042)."""
    src = """
// <vc-preamble>
// </vc-preamble>
// <vc-spec>
method Abs(x: int) returns (y: int)
  ensures x >= 0 ==> x == y
  ensures x < 0 ==> x + y == 0
// </vc-spec>
// <vc-code>
{ assume {:axiom} false; }
// </vc-code>
"""
    out = translate(src, "DD0042")
    # The translation must contain a hole and reference x>=0 and x<0.
    assert "?hole" in out
    assert "def Abs" in out
    # No unhandled Dafny operators.
    assert "==>" not in out
    assert "<==>" not in out


def test_multi_line_ensures_clause():
    """ensures clauses can span multiple lines (DV0181 pattern). The translator
    must not truncate at the first newline."""
    src = """
// <vc-preamble>
// </vc-preamble>
// <vc-spec>
method triple(x: int) returns (result: int)
    ensures
        result / 3 == x &&
        result / 3 * 3 == result
// </vc-spec>
// <vc-code>
{ assume {:axiom} false; }
// </vc-code>
"""
    out = translate(src, "DV0181")
    # Both conjuncts must appear; nothing should be left dangling.
    assert "result / 3 == x" in out
    assert "result / 3 * 3 == result" in out
    # No trailing `&&` (was the bug).
    assert "&&)" not in out
    assert "&&}" not in out


def test_rejects_typed_quantifier():
    """`forall j: int :: ...` is a quantifier even though it has a typed
    binder — the early v1 regex required `::` to be the next thing after the
    binder name, which missed this form."""
    src = """
// <vc-preamble>
// </vc-preamble>
// <vc-spec>
method M(n: int) returns (r: bool)
  ensures r == forall j: int :: 2 <= j && j < n
// </vc-spec>
// <vc-code>
{ assume {:axiom} false; }
// </vc-code>
"""
    with pytest.raises(TranslationError, match="quantifier"):
        translate(src, "TEST")


def test_rejects_set_literal():
    """Dafny `month in {1, 3, 5}` uses a set literal — outside the int/bool
    subset. The translator must reject it instead of emitting garbage."""
    src = """
// <vc-preamble>
// </vc-preamble>
// <vc-spec>
method M(month: int) returns (r: bool)
  ensures r == (month in {1, 3, 5, 7, 8, 10, 12})
// </vc-spec>
// <vc-code>
{ assume {:axiom} false; }
// </vc-code>
"""
    with pytest.raises(TranslationError, match="set literal"):
        translate(src, "TEST")


def test_translates_constant_seven_passes_aeon_parser():
    """Smoke test: DD0080 (`returns 7`) translates and aeon can parse the result.

    This is the simplest possible non-trivial round-trip: translator + aeon
    parser + aeon type-checker. We don't run synthesis (too slow for CI), just
    confirm the .ae file is accepted.
    """
    src = """
// <vc-preamble>
// </vc-preamble>
// <vc-spec>
method M(x: int) returns (seven: int)
  ensures seven == 7
// </vc-spec>
// <vc-code>
{ assume {:axiom} false; }
// </vc-code>
"""
    out = translate(src, "DD0080")
    assert "def M" in out
    assert "?hole" in out

    # Replace the hole with the trivial answer and ask aeon to type-check it.
    aeon_src = out.replace("?hole", "7")
    from aeon.facade.driver import AeonConfig, AeonDriver  # noqa: E402
    from aeon.logger.logger import setup_logger  # noqa: E402
    from aeon.synthesis.uis.terminal import TerminalUI  # noqa: E402

    setup_logger()  # registers the custom TIME log level
    cfg = AeonConfig(
        synthesizer="tdsyn_enumerative",
        synthesis_ui=TerminalUI(),
        synthesis_budget=1,
        no_main=True,
    )
    errors = AeonDriver(cfg).parse(aeon_code=aeon_src)
    assert not errors, f"aeon rejected the translated code: {errors}"
