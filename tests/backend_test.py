from __future__ import annotations

from aeon.backend.evaluator import EvaluationContext, eval
from aeon.core.terms import Literal, TypeAbstraction, TypeApplication
from aeon.core.types import BaseKind, BaseType
from aeon.frontend.parser import parse_term


def test_literal():
    assert eval(parse_term("1")) == 1
    assert eval(parse_term("true")) is True
    assert eval(parse_term("false")) is False
    assert eval(parse_term("1.0")) == 1.0
    assert eval(parse_term(""" "hello"  """)) == "hello"

    assert eval(Literal(value=(2, 3), type=BaseType("Tuple"))) == (2, 3)


def test_application():
    assert eval(parse_term("(\\x -> x) 1")) == 1
    assert eval(parse_term("(\\x -> (\\y -> x)) 1 2")) == 1
    assert eval(parse_term("(\\x -> (\\y -> y)) 1 2")) == 2

    assert eval(parse_term("(\\x -> (\\y -> y)) 1 a"), EvaluationContext({"a": 2})) == 2


def test_if():
    assert eval(parse_term("if true then 1 else 0")) == 1
    assert eval(parse_term("if false then 1 else 0")) == 0
    assert eval(parse_term("if false then 1 else if true then 2 else 3")) == 2


def test_if_str():
    assert eval(parse_term('if true then "ola" else "adeus"')) == "ola"
    assert eval(parse_term('if false then "ola" else "adeus"')) == "adeus"


def test_let():
    assert eval(parse_term("let a = 1 in a")) == 1
    assert eval(parse_term("let b = 1 in 2")) == 2


def test_rec():
    assert (
        eval(
            parse_term("let fact : (x:Int) -> Int = (\\n -> (if n > 0 then 1 * fact (n-1) else 1)) in fact 3"),
            EvaluationContext(
                {">": lambda x: lambda y: x > y, "-": lambda x: lambda y: x - y, "*": lambda x: lambda y: x * y}
            ),
        )
        == 1
    )


def test_type_abs_app():
    tabs = TypeAbstraction("t", BaseKind(), parse_term("1"))
    tapp = TypeApplication(tabs, BaseType("Int"))
    assert eval(tapp) == 1
