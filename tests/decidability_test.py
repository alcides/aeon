"""Tests for aeon.verification.decidability — warning when refinements leave
the decidable fragment Liquid Types target (issue #438)."""

from __future__ import annotations

from aeon.core.liquid import (
    LiquidApp,
    LiquidLiteralInt,
    LiquidVar,
)
from aeon.core.types import RefinedType, t_int
from aeon.facade.api import UndecidableRefinementError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SynthesisUI
from aeon.utils.location import FileLocation
from aeon.utils.name import Name
from aeon.verification.decidability import (
    DecidabilityWarning,
    classify_refinement,
    collect_decidability_warnings,
)

setup_logger()

x = Name("x")
y = Name("y")
v = Name("v")

LOC = FileLocation("test.ae", start=(1, 1), end=(1, 10))


def _app(op: str, *args):
    return LiquidApp(Name(op, 0), list(args), loc=LOC)


# ---------------------------------------------------------------------------
# classify_refinement — multiplication
# ---------------------------------------------------------------------------


def test_variable_times_variable_warns():
    warnings = classify_refinement(_app("*", LiquidVar(x), LiquidVar(y)))
    assert len(warnings) == 1
    assert warnings[0].construct == "nonlinear multiplication"
    assert warnings[0].location == LOC


def test_constant_times_variable_no_warning():
    assert classify_refinement(_app("*", LiquidLiteralInt(2), LiquidVar(x))) == []


def test_variable_times_constant_no_warning():
    assert classify_refinement(_app("*", LiquidVar(x), LiquidLiteralInt(2))) == []


def test_constant_times_constant_no_warning():
    assert classify_refinement(_app("*", LiquidLiteralInt(2), LiquidLiteralInt(3))) == []


# ---------------------------------------------------------------------------
# classify_refinement — division / modulo
# ---------------------------------------------------------------------------


def test_division_by_variable_warns():
    warnings = classify_refinement(_app("/", LiquidVar(x), LiquidVar(y)))
    assert len(warnings) == 1
    assert warnings[0].construct == "non-constant division"


def test_division_by_constant_no_warning():
    assert classify_refinement(_app("/", LiquidVar(x), LiquidLiteralInt(4))) == []


def test_modulo_by_variable_warns():
    warnings = classify_refinement(_app("%", LiquidVar(x), LiquidVar(y)))
    assert len(warnings) == 1
    assert warnings[0].construct == "non-constant modulo"


def test_modulo_by_constant_no_warning():
    assert classify_refinement(_app("%", LiquidVar(x), LiquidLiteralInt(2))) == []


# ---------------------------------------------------------------------------
# classify_refinement — exponentiation / quantifiers (defensive)
# ---------------------------------------------------------------------------


def test_exponentiation_warns():
    warnings = classify_refinement(_app("**", LiquidVar(x), LiquidVar(y)))
    assert len(warnings) == 1
    assert warnings[0].construct == "exponentiation"


def test_exponentiation_by_constant_still_warns():
    warnings = classify_refinement(_app("**", LiquidVar(x), LiquidLiteralInt(2)))
    assert len(warnings) == 1
    assert warnings[0].construct == "exponentiation"


def test_quantifier_warns():
    warnings = classify_refinement(_app("forall", LiquidVar(x)))
    assert len(warnings) == 1
    assert warnings[0].construct == "quantifier"


# ---------------------------------------------------------------------------
# classify_refinement — purely linear predicates produce no warning
# ---------------------------------------------------------------------------


def test_linear_addition_no_warning():
    # x + y > 0
    pred = _app(">", _app("+", LiquidVar(x), LiquidVar(y)), LiquidLiteralInt(0))
    assert classify_refinement(pred) == []


def test_linear_scaled_no_warning():
    # 2 * x + 3 * y = 0
    pred = _app(
        "=",
        _app("+", _app("*", LiquidLiteralInt(2), LiquidVar(x)), _app("*", LiquidLiteralInt(3), LiquidVar(y))),
        LiquidLiteralInt(0),
    )
    assert classify_refinement(pred) == []


def test_comparison_only_no_warning():
    pred = _app("<", LiquidVar(x), LiquidVar(y))
    assert classify_refinement(pred) == []


# ---------------------------------------------------------------------------
# classify_refinement — nested products are found
# ---------------------------------------------------------------------------


def test_nested_product_in_comparison_warns():
    # (x * y) > 0
    pred = _app(">", _app("*", LiquidVar(x), LiquidVar(y)), LiquidLiteralInt(0))
    warnings = classify_refinement(pred)
    assert len(warnings) == 1
    assert warnings[0].construct == "nonlinear multiplication"


# ---------------------------------------------------------------------------
# collect_decidability_warnings — type/term walking, dedup, file filter
# ---------------------------------------------------------------------------


def test_collect_dedups_by_span_and_construct():
    from aeon.core.terms import Rec, Literal

    refinement = _app("*", LiquidVar(x), LiquidVar(y))
    refined = RefinedType(v, t_int, refinement)
    # Same refined type appears in two places (signature + annotation-like reuse).
    inner = Rec(Name("g"), refined, Literal(0, t_int), Literal(0, t_int))
    outer = Rec(Name("f"), refined, inner, Literal(0, t_int))
    warnings = collect_decidability_warnings(outer, source_path="test.ae")
    assert len(warnings) == 1


def test_collect_filters_to_source_file():
    from aeon.core.terms import Rec, Literal

    other_loc = FileLocation("other.ae", start=(2, 2), end=(2, 5))
    refinement = LiquidApp(Name("*", 0), [LiquidVar(x), LiquidVar(y)], loc=other_loc)
    refined = RefinedType(v, t_int, refinement)
    term = Rec(Name("f"), refined, Literal(0, t_int), Literal(0, t_int))
    assert collect_decidability_warnings(term, source_path="test.ae") == []
    assert len(collect_decidability_warnings(term, source_path="other.ae")) == 1


def test_warning_str_is_readable():
    w = DecidabilityWarning(LOC, "nonlinear multiplication", "because reasons")
    assert "nonlinear multiplication" in str(w)
    assert "because reasons" in str(w)


# ---------------------------------------------------------------------------
# Driver integration
# ---------------------------------------------------------------------------


def _driver(source: str, *, strict: bool = False):
    cfg = AeonConfig(
        synthesizer="none",
        synthesis_ui=SynthesisUI(),
        synthesis_budget=0,
        strict_decidable=strict,
    )
    driver = AeonDriver(cfg)
    errors = list(driver.parse(aeon_code=source))
    return driver, errors


def test_driver_warns_on_nonlinear_refinement():
    source = "def mul (x:Int) (y:Int) : {v:Int | v = x * y} := x * y;\ndef main (_:Int) : Unit := print 0;"
    driver, errors = _driver(source)
    assert not errors, errors
    assert len(driver.decidability_warnings) == 1
    assert driver.decidability_warnings[0].construct == "nonlinear multiplication"


def test_driver_no_warning_on_linear_refinement():
    source = "def f (x:Int) : {v:Int | v = x * 2} := x * 2;\ndef main (_:Int) : Unit := print 0;"
    driver, errors = _driver(source)
    assert not errors, errors
    assert driver.decidability_warnings == []


def test_driver_strict_turns_warning_into_error():
    source = "def mul (x:Int) (y:Int) : {v:Int | v = x * y} := x * y;\ndef main (_:Int) : Unit := print 0;"
    _driver_obj, errors = _driver(source, strict=True)
    assert any(isinstance(e, UndecidableRefinementError) for e in errors), errors


def test_driver_strict_accepts_linear_refinement():
    source = "def f (x:Int) : {v:Int | v = x * 2} := x * 2;\ndef main (_:Int) : Unit := print 0;"
    _driver_obj, errors = _driver(source, strict=True)
    assert not errors, errors
