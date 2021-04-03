from aeon.core.substitutions import substitution, substitution_in_type
from aeon.frontend.parser import parse_term, parse_type


def test_substitution_term():
    t = parse_term("a + 1")
    assert substitution(t, parse_term("2"), "a") == parse_term("2 + 1")


def test_substitution_term_shadow():
    t = parse_term(r"\a -> a + 1")
    assert substitution(t, parse_term("2"), "a") == parse_term(r"\a -> a + 1")


def test_substitution_term_let():
    t = parse_term(r"let b = 1 in a")
    assert substitution(t, parse_term("2"), "a") == parse_term(r"let b = 1 in 2")


def test_substitution_term_shadow_let():
    t = parse_term(r"let a = 1 in a")
    assert substitution(t, parse_term("2"), "a") == parse_term(r"let a = 1 in a")


def test_substitution_type_shadow():
    ty = parse_type(r"{x : Int | x > 0}")
    assert substitution_in_type(ty, parse_term("3"), "x") == parse_type(
        r"{x : Int | x > 0}"
    )


def test_substitution_type():
    ty = parse_type(r"{x : Int | x > z}")
    assert substitution_in_type(ty, parse_term("3"), "z") == parse_type(
        r"{x : Int | x > 3}"
    )


def test_substitution_type_abs_shadow():
    ty = parse_type(r"(y:Int) -> {x : Int | x > y}")
    assert substitution_in_type(ty, parse_term("3"), "y") == parse_type(
        r"(y:Int) -> {x : Int | x > y}"
    )


def test_substitution_type_abs():
    ty = parse_type(r"(y:Int) -> {x : Int | x > z}")
    assert substitution_in_type(ty, parse_term("3"), "z") == parse_type(
        r"(y:Int) -> {x : Int | x > 3}"
    )


def test_substitution_autorename():
    ty = parse_type(r"(y:Int) -> {x : Int | x > z}")
    assert substitution_in_type(ty, parse_term("x"), "z") == parse_type(
        r"(y:Int) -> {x1 : Int | x1 > x}"
    )


def test_substitution_autorename_ref():
    ty = parse_type(r"(y:Int) -> {x : Int | y > z}")
    assert substitution_in_type(ty, parse_term("y"), "z") == parse_type(
        r"(y1:Int) -> {x : Int | y1 > y}"
    )
