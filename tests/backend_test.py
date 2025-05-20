from __future__ import annotations

from aeon.core.bind import bind_term

from aeon.utils.name import Name

from aeon.backend.evaluator import EvaluationContext, eval
from aeon.core.terms import Literal, Term, TypeAbstraction, TypeApplication
from aeon.core.types import BaseKind, BaseType
from aeon.frontend.parser import parse_term


def weval(t: Term, ctx: EvaluationContext = EvaluationContext()):
    return eval(bind_term(t, []), ctx)


def test_literal():
    assert weval(parse_term("1")) == 1
    assert weval(parse_term("true")) is True
    assert weval(parse_term("false")) is False
    assert weval(parse_term("1.0")) == 1.0
    assert weval(parse_term(""" "hello"  """)) == "hello"

    assert weval(Literal(value=(2, 3), type=BaseType("Tuple"))) == (2, 3)


def test_application():
    assert weval(parse_term("(\\x -> x) 1")) == 1
    assert weval(parse_term("(\\x -> (\\y -> x)) 1 2")) == 1
    assert weval(parse_term("(\\x -> (\\y -> y)) 1 2")) == 2

    assert (
        weval(
            parse_term("(\\x -> (\\y -> y)) 1 a"),
            EvaluationContext({Name("a"): 2}),
        )
        == 2
    )


def test_if():
    assert weval(parse_term("if true then 1 else 0")) == 1
    assert weval(parse_term("if false then 1 else 0")) == 0
    assert weval(parse_term("if false then 1 else if true then 2 else 3")) == 2


def test_if_str():
    assert weval(parse_term('if true then "ola" else "adeus"')) == "ola"
    assert weval(parse_term('if false then "ola" else "adeus"')) == "adeus"


def test_let():
    assert weval(parse_term("let a = 1 in a")) == 1
    assert weval(parse_term("let b = 1 in 2")) == 2


def test_rec():
    assert (
        weval(
            parse_term(
                "let fact : (x:Int) -> Int = (\\n -> (if n > 0 then 1 * fact (n-1) else 1)) in fact 3",
            ),
            EvaluationContext(
                {
                    Name(">", 0): lambda x: lambda y: x > y,
                    Name("-", 0): lambda x: lambda y: x - y,
                    Name("*", 0): lambda x: lambda y: x * y,
                },
            ),
        )
        == 1
    )


def test_type_abs_app():
    tabs = TypeAbstraction(Name("t"), BaseKind(), parse_term("1"))
    tapp = TypeApplication(tabs, BaseType("Int"))
    assert weval(tapp) == 1
