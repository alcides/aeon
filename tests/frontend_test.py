from __future__ import annotations

from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidVar
from aeon.core.terms import Abstraction
from aeon.core.terms import Annotation
from aeon.core.terms import Application
from aeon.core.terms import If
from aeon.core.terms import Let
from aeon.core.terms import TypeAbstraction
from aeon.core.terms import TypeApplication
from aeon.core.terms import Var
from aeon.core.types import AbstractionType
from aeon.core.types import BaseKind
from aeon.core.types import RefinedType
from aeon.core.types import t_bool
from aeon.core.types import t_int
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar

from aeon.frontend.parser import parse_term
from aeon.frontend.parser import parse_type
from aeon.utils.ast_helpers import false
from aeon.utils.ast_helpers import i0
from aeon.utils.ast_helpers import i1
from aeon.utils.ast_helpers import i2
from aeon.utils.ast_helpers import mk_binop
from aeon.utils.ast_helpers import true


def test_basetypes():
    assert parse_type("Int") == t_int
    assert parse_type("Bool") == t_bool
    print(type(parse_type("a")), "..")
    assert parse_type("a") == TypeVar("a")
    assert parse_type("(a)") == TypeVar("a")
    assert parse_type("((a))") == TypeVar("a")


def test_abstractiontypes():
    assert parse_type("(x:Int) -> Int") == AbstractionType("x", t_int, t_int)
    assert parse_type("(y:Int) -> Int") != AbstractionType("x", t_int, t_int)
    assert parse_type("(x:Bool) -> Int") != AbstractionType("x", t_int, t_int)
    assert parse_type("(x:Bool) -> (y:Bool) -> Int") == AbstractionType(
        "x",
        t_bool,
        AbstractionType("y", t_bool, t_int),
    )


def test_refinedtypes():
    assert parse_type("{x:Int|true}") == RefinedType(
        "x",
        t_int,
        LiquidLiteralBool(True),
    )
    assert parse_type("{y:Int|y > x}") == RefinedType(
        "y",
        t_int,
        LiquidApp(">", [LiquidVar("y"), LiquidVar("x")]),
    )
    assert parse_type("{y:Int | y == 1 + 1}") == RefinedType(
        "y",
        t_int,
        LiquidApp(
            "==",
            [
                LiquidVar("y"),
                LiquidApp(
                    "+",
                    [
                        LiquidLiteralInt(1),
                        LiquidLiteralInt(1),
                    ],
                ),
            ],
        ),
    )


def test_literals():
    assert parse_term("1") == i1
    assert parse_term("true") == true
    assert parse_term("false") == false


def test_operators():
    assert parse_term("-a") == mk_binop(lambda: "t", "-", i0, Var("a"))

    assert parse_term("!true") == Application(Var("!"), true)

    assert parse_term("1 == 1") == mk_binop(lambda: "t", "==", i1, i1)
    assert parse_term("1 != 1") == mk_binop(lambda: "t", "!=", i1, i1)
    assert parse_term("true && true") == mk_binop(
        lambda: "t",
        "&&",
        true,
        true,
    )
    assert parse_term("true || true") == mk_binop(
        lambda: "t",
        "||",
        true,
        true,
    )

    assert parse_term("0 < 1") == mk_binop(lambda: "t", "<", i0, i1)
    assert parse_term("0 > 1") == mk_binop(lambda: "t", ">", i0, i1)
    assert parse_term("0 <= 1") == mk_binop(lambda: "t", "<=", i0, i1)
    assert parse_term("0 >= 1") == mk_binop(lambda: "t", ">=", i0, i1)

    assert parse_term("true --> false") == mk_binop(
        lambda: "t",
        "-->",
        true,
        false,
    )

    assert parse_term("1 + 1") == mk_binop(lambda: "t", "+", i1, i1)
    assert parse_term("1 - 1") == mk_binop(lambda: "t", "-", i1, i1)
    assert parse_term("1 * 1") == mk_binop(lambda: "t", "*", i1, i1)
    assert parse_term("1 / 1") == mk_binop(lambda: "t", "/", i1, i1)
    assert parse_term("1 % 1") == mk_binop(lambda: "t", "%", i1, i1)


def test_let():
    assert parse_term("let x = 1 in x") == Let("x", i1, Var("x"))


def test_if():
    assert parse_term("if true then 1 else 2") == If(true, i1, i2)


def test_abs():
    assert parse_term("\\x -> x") == Abstraction("x", Var("x"))


def test_ann():
    assert parse_term("\\x -> (x : Int)") == Abstraction(
        "x",
        Annotation(Var("x"), t_int),
    )


def test_poly_parse():
    assert parse_type("forall a:B, (_:a) -> a") == TypePolymorphism(
        "a",
        BaseKind(),
        AbstractionType("_", TypeVar("a"), TypeVar("a")),
    )


def test_poly_abs():
    assert parse_term("Λa:B => 1") == TypeAbstraction(
        "a",
        BaseKind(),
        parse_term("1"),
    )


def test_poly_abs_plus():
    assert parse_term("Λa:B => \\ x -> x + 1") == TypeAbstraction(
        "a",
        BaseKind(),
        parse_term("\\ x -> x + 1"),
    )


def test_poly_app():
    one_a = TypeApplication(parse_term("1"), TypeVar("a"))
    e = TypeAbstraction("a", BaseKind(), one_a)
    assert parse_term("(Λa:B => 1[a])[Int]") == TypeApplication(e, t_int)
