from typing import Optional
from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt, LiquidVar
from aeon.core.terms import Literal
from aeon.core.types import AbstractionType, BaseType, RefinedType, t_int, t_bool
from aeon.frontend.parser import parse_term, parse_type


def test_basetypes():
    assert parse_type("Int") == t_int
    assert parse_type("Bool") == t_bool
    assert parse_type("a") == BaseType("a")
    assert parse_type("(a)") == BaseType("a")
    assert parse_type("((a))") == BaseType("a")


def test_abstractiontypes():
    assert parse_type("(x:Int) -> Int") == AbstractionType("x", t_int, t_int)
    assert parse_type("(y:Int) -> Int") != AbstractionType("x", t_int, t_int)
    assert parse_type("(x:Bool) -> Int") != AbstractionType("x", t_int, t_int)
    assert parse_type("(x:Bool) -> (y:Bool) -> Int") == AbstractionType(
        "x", t_bool, AbstractionType("y", t_bool, t_int))


def test_refinedtypes():
    assert parse_type("{x:Int|true}") == RefinedType("x", t_int,
                                                     LiquidLiteralBool(True))
    assert parse_type("{y:Int|y > x}") == RefinedType(
        "y", t_int, LiquidApp(">",
                              [LiquidVar("y"), LiquidVar("x")]))
    assert parse_type("{y:Int | y == 1 + 1}") == RefinedType(
        "y", t_int,
        LiquidApp("==", [
            LiquidVar("y"),
            LiquidApp("+", [LiquidLiteralInt(1),
                            LiquidLiteralInt(1)])
        ]))


def test_literals():
    one = parse_term("1")
    assert isinstance(one, Literal)
    assert one.type == t_int
    assert one.value == 1

    tt = parse_term("true")
    assert isinstance(tt, Literal)
    assert tt.type == t_bool
    assert tt.value == True

    ff = parse_term("false")
    assert isinstance(ff, Literal)
    assert ff.type == t_bool
    assert ff.value == False
