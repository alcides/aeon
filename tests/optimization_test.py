from __future__ import annotations

from aeon.optimization.normal_form import optimize
from aeon.frontend.parser import parse_term


def eq(source, expected):
    p1 = parse_term(source)
    p2 = parse_term(expected)
    po = optimize(p1)
    assert po == p2


def test_opt_if():
    eq("if true then 1 else 0", "1")
    eq("if false then 1 else 0", "0")
    eq("if false then 2 else if true then 1 else 0", "1")


def test_opt_app():
    eq("(\\x -> 1) 2", "1")
    eq("(\\x -> x) 2", "2")

    eq("(\\x -> (\\y -> x)) 2 3", "2")


def test_opt_let():
    eq("let x = 2 in x", "2")


def test_opt_mix():
    eq("let x = (\\y -> y) in (if true then x 3 else x 4)", "3")


def test_opt_tapp():
    eq("(Λa:B =>1)[Int]", "1")


def test_opt_net():
    nh = """native "hello" """
    eq(nh, nh)
    eq("x", "x")
    eq("\\x -> x", "\\x -> x")


def test_opt_and():
    eq("true && true", "true")
    eq("a && true", "a")
    eq("true && a", "a")


def test_opt_if_and():
    eq("if true && true then a else b", "a")
    eq("if false && true then a else b", "b")


def test_opt_plus():
    eq("a+0", "a")
    eq("0+a", "a")
    eq("1+1", "2")


def test_opt_mul():
    eq("a*0", "0")
    eq("0*a", "0")
    eq("1*a", "a")
    eq("a*1*1", "a")
    eq("3*2", "6")
    eq("a*(2-2)", "0")


def test_opt_op():
    eq("1==1", "true")
    eq("1!=1", "false")
    eq("1>=1", "true")
    eq("1>1", "false")
    eq("1<=1", "true")
    eq("1<1", "false")
    eq("1*1", "1")
    eq("1+1", "2")
    eq("1-1", "0")
    eq("true && false", "false")
    eq("true || false", "true")
