from __future__ import annotations

from aeon.core.substitutions import substitution
from aeon.core.substitutions import substitution_in_type
from aeon.core.parser import parse_term
from aeon.core.parser import parse_type
from aeon.utils.name import Name
from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
from aeon.core.substitutions import substitution_in_liquid


def test_substitution_term():
    t = parse_term("a + 1")
    assert substitution(t, parse_term("2"), Name("a")) == parse_term("2 + 1")


def test_substitution_term_shadow():
    t = parse_term(r"fun a => a + 1")
    assert substitution(t, parse_term("2"), Name("a")) == parse_term(r"fun a => a + 1")


def test_substitution_term_let():
    t = parse_term(r"let b = 1 in a")
    assert substitution(t, parse_term("2"), Name("a")) == parse_term(r"let b = 1 in 2")


def test_substitution_term_shadow_let():
    t = parse_term(r"let a = 1 in a")
    assert substitution(t, parse_term("2"), Name("a")) == parse_term(r"let a = 1 in a")


def test_substitution_type_shadow():
    ty = parse_type(r"{x : Int | x > 0}")
    assert substitution_in_type(ty, parse_term("3"), Name("x")) == parse_type(
        r"{x : Int | x > 0}",
    )


def test_substitution_type():
    ty = parse_type(r"{x : Int | x > z}")
    assert substitution_in_type(ty, parse_term("3"), Name("z")) == parse_type(
        r"{x : Int | x > 3}",
    )


def test_substitution_type_abs_shadow():
    ty = parse_type(r"(y:Int) -> {x : Int | x > y}")
    assert substitution_in_type(ty, parse_term("3"), Name("y")) == parse_type(
        r"(y:Int) -> {x : Int | x > y}",
    )


def test_substitution_type_abs():
    ty = parse_type(r"(y:Int) -> {x : Int | x > z}")
    assert substitution_in_type(ty, parse_term("3"), Name("z")) == parse_type(
        r"(y:Int) -> {x : Int | x > 3}",
    )


def test_liquid_substitution_preserves_shared_subterms():
    x = Name("x")
    term = LiquidVar(x)
    # Only 17 distinct nodes, but over 2**16 paths if sharing is lost.
    # Keep the depth bounded so a regression fails without hanging CI.
    for _ in range(16):
        term = LiquidApp(Name("+"), [term, term])
    replacement = LiquidLiteralInt(7)
    result = substitution_in_liquid(term, replacement, x)
    for _ in range(16):
        assert isinstance(result, LiquidApp)
        assert result.args[0] is result.args[1]
        result = result.args[0]
    assert result is replacement


def test_liquid_substitution_memo_is_per_call():
    x, y = Name("x", 1), Name("x", 2)
    term = LiquidApp(Name("+"), [LiquidVar(x), LiquidVar(y)])
    first = substitution_in_liquid(term, LiquidLiteralInt(7), x)
    second = substitution_in_liquid(term, LiquidLiteralInt(9), y)
    assert first == LiquidApp(Name("+"), [LiquidLiteralInt(7), LiquidVar(y)])
    assert second == LiquidApp(Name("+"), [LiquidVar(x), LiquidLiteralInt(9)])
