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
from aeon.frontend.anf_converter import ensure_anf
from aeon.frontend.parser import parse_term
from aeon.frontend.parser import parse_type
from aeon.utils.ast_helpers import false
from aeon.utils.ast_helpers import i0
from aeon.utils.ast_helpers import i1
from aeon.utils.ast_helpers import i2
from aeon.utils.ast_helpers import is_anf
from aeon.utils.ast_helpers import mk_binop
from aeon.utils.ast_helpers import true
from aeon.utils.name import Name

x_name = Name("x")
y_name = Name("y")


def test_basetypes():
    assert parse_type("Int") == t_int
    assert parse_type("Bool") == t_bool
    assert parse_type("a") == TypeVar(Name("a"))
    assert parse_type("(a)") == TypeVar(Name("a"))
    assert parse_type("((a))") == TypeVar(Name("a"))


def test_abstractiontypes():
    assert parse_type("(x:Int) -> Int") == AbstractionType(x_name, t_int, t_int)
    assert parse_type("(y:Int) -> Int") != AbstractionType(x_name, t_int, t_int)
    assert parse_type("(x:Bool) -> Int") != AbstractionType(x_name, t_int, t_int)
    assert parse_type("(x:Bool) -> (y:Bool) -> Int") == AbstractionType(
        x_name,
        t_bool,
        AbstractionType(y_name, t_bool, t_int),
    )


def test_refinedtypes():
    assert parse_type("{x:Int|true}") == RefinedType(
        x_name,
        t_int,
        LiquidLiteralBool(True),
    )
    assert parse_type("{y:Int|y > x}") == RefinedType(
        y_name,
        t_int,
        LiquidApp(Name(">", 0), [LiquidVar(y_name), LiquidVar(x_name)]),
    )
    assert parse_type("{y:Int | y == 1 + 1}") == RefinedType(
        y_name,
        t_int,
        LiquidApp(
            Name("==", 0),
            [
                LiquidVar(y_name),
                LiquidApp(Name("+", 0), [LiquidLiteralInt(1), LiquidLiteralInt(1)]),
            ],
        ),
    )


def test_literals():
    assert parse_term("1") == i1
    assert parse_term("true") == true
    assert parse_term("false") == false


def test_operators():
    assert parse_term("-a") == mk_binop(lambda: "t", "-", i0, Var(Name("a")))

    assert parse_term("!true") == Application(Var(Name("!", 0)), true)

    assert parse_term("1 == 1") == mk_binop(lambda: "t", "==", i1, i1)
    assert parse_term("1 != 1") == mk_binop(lambda: "t", "!=", i1, i1)
    assert parse_term("true && true") == mk_binop(lambda: "t", "&&", true, true)
    assert parse_term("true || true") == mk_binop(lambda: "t", "||", true, true)

    assert parse_term("0 < 1") == mk_binop(lambda: "t", "<", i0, i1)
    assert parse_term("0 > 1") == mk_binop(lambda: "t", ">", i0, i1)
    assert parse_term("0 <= 1") == mk_binop(lambda: "t", "<=", i0, i1)
    assert parse_term("0 >= 1") == mk_binop(lambda: "t", ">=", i0, i1)

    assert parse_term("true --> false") == mk_binop(lambda: "t", "-->", true, false)

    assert parse_term("1 + 1") == mk_binop(lambda: "t", "+", i1, i1)
    assert parse_term("1 - 1") == mk_binop(lambda: "t", "-", i1, i1)
    assert parse_term("1 * 1") == mk_binop(lambda: "t", "*", i1, i1)
    assert parse_term("1 / 1") == mk_binop(lambda: "t", "/", i1, i1)
    assert parse_term("1 % 1") == mk_binop(lambda: "t", "%", i1, i1)


def test_precedence():
    t1 = parse_term("1 + 2 * 0")
    at1 = ensure_anf(t1)
    assert is_anf(at1)


def test_let():
    assert parse_term("let x = 1 in x") == Let(x_name, i1, Var(x_name))


def test_if():
    assert parse_term("if true then 1 else 2") == If(true, i1, i2)


def test_abs():
    assert parse_term("\\x -> x") == Abstraction(x_name, Var(x_name))


def test_ann():
    assert parse_term("\\x -> (x : Int)") == Abstraction(
        x_name,
        Annotation(Var(x_name), t_int),
    )


def test_poly_parse():
    a_name = Name("a")
    assert parse_type("forall a:B, (_:a) -> a") == TypePolymorphism(
        a_name,
        BaseKind(),
        AbstractionType(Name("_"), TypeVar(a_name), TypeVar(a_name)),
    )


def test_poly_abs():
    assert parse_term("Λa:B => 1") == TypeAbstraction(Name("a"), BaseKind(), parse_term("1"))


def test_poly_abs_plus():
    assert parse_term("Λa:B => \\ x -> x + 1") == TypeAbstraction(
        Name("a"),
        BaseKind(),
        parse_term("\\ x -> x + 1"),
    )


def test_poly_app():
    one_a = TypeApplication(parse_term("1"), TypeVar(Name("a")))
    e = TypeAbstraction(Name("a"), BaseKind(), one_a)
    assert parse_term("(Λa:B => 1[a])[Int]") == TypeApplication(e, t_int)
