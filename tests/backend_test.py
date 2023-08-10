from __future__ import annotations

from aeon.backend.evaluator import eval
from aeon.frontend.parser import parse_term


def test_literal():
    assert eval(parse_term("1")) == 1
    assert eval(parse_term("true")) is True
    assert eval(parse_term("false")) is False


def test_application():
    assert eval(parse_term("(\\x -> x) 1")) == 1


def test_if():
    assert eval(parse_term("if true then 1 else 0")) == 1
    assert eval(parse_term("if false then 1 else 0")) == 0


def test_if_str():
    assert eval(parse_term('if true then "ola" else "adeus"')) == "ola"
    assert eval(parse_term('if false then "ola" else "adeus"')) == "adeus"


def test_let():
    assert eval(parse_term("let a = 1 in a")) == 1
    assert eval(parse_term("let b = 1 in 2")) == 2
