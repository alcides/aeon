from typing import Optional
from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt, LiquidVar
from aeon.core.terms import Abstraction, Application, If, Let, Literal, Term, Var
from aeon.core.types import AbstractionType, BaseType, RefinedType, t_int, t_bool
from aeon.frontend.parser import parse_term, parse_type
from aeon.utils.ast_helpers import mk_binop, i0, i1, i2, true, false


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
        "y",
        t_int,
        LiquidApp(
            "==",
            [
                LiquidVar("y"),
                LiquidApp("+", [LiquidLiteralInt(1),
                                LiquidLiteralInt(1)]),
            ],
        ),
    )


def test_literals():
    assert parse_term("1") == i1
    assert parse_term("true") == true
    assert parse_term("false") == false


def test_operators():
    assert parse_term("-1") == mk_binop("-", i0, i1)

    assert parse_term("!true") == Application(Var("!"), true)

    assert parse_term("1 == 1") == mk_binop("==", i1, i1)
    assert parse_term("1 != 1") == mk_binop("!=", i1, i1)
    assert parse_term("true && true") == mk_binop("&&", true, true)
    assert parse_term("true || true") == mk_binop("||", true, true)

    assert parse_term("0 < 1") == mk_binop("<", i0, i1)
    assert parse_term("0 > 1") == mk_binop(">", i0, i1)
    assert parse_term("0 <= 1") == mk_binop("<=", i0, i1)
    assert parse_term("0 >= 1") == mk_binop(">=", i0, i1)

    assert parse_term("true --> false") == mk_binop("-->", true, false)

    assert parse_term("1 + 1") == mk_binop("+", i1, i1)
    assert parse_term("1 - 1") == mk_binop("-", i1, i1)
    assert parse_term("1 * 1") == mk_binop("*", i1, i1)
    assert parse_term("1 / 1") == mk_binop("/", i1, i1)
    assert parse_term("1 % 1") == mk_binop("%", i1, i1)


def test_precedence():
    assert parse_term("1 + 2 * 0") == mk_binop("+", i1, mk_binop("*", i2, i0))


def test_let():
    assert parse_term("let x = 1 in x") == Let("x", i1, Var("x"))


def test_if():
    assert parse_term("if true then 1 else 2") == If(true, i1, i2)


def test_abs():
    assert parse_term("\\x : Int -> x") == Abstraction("x", t_int, Var("x"))
