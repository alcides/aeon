from __future__ import annotations

from aeon.optimization.normal_form import optimize
from aeon.optimization.whnf import whnf
from aeon.core.parser import parse_term


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
    eq("(fun x => 1) 2", "1")
    eq("(fun x => x) 2", "2")

    eq("(fun x => (fun y => x)) 2 3", "2")


def test_opt_let():
    eq("let x = 2 in x", "2")


def test_opt_mix():
    eq("let x = (fun y => y) in (if true then x 3 else x 4)", "3")


def test_opt_tapp():
    eq("(Λa:B =>1)[Int]", "1")


def test_opt_net():
    nh = """native "hello" """
    eq(nh, nh)
    eq("x", "x")
    eq("fun x => x", "fun x => x")


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


def test_whnf_peels_annotations():
    t = parse_term("(fun x => 1) 2")
    assert whnf(t) == parse_term("1")


def test_whnf_does_not_descend_into_abstraction_body():
    t = parse_term("fun x => (fun y => y) 0")
    assert whnf(t) == t


def test_opt_native_lambda():
    eq('(native "lambda x: x") 1', "1")
    eq('(native "lambda x: x + 1") 2', "3")
    eq('(native "lambda x: lambda y: x + y") 1 2', "3")


def test_opt_native_lambda_with_var():
    eq('(native "lambda x: x") y', "y")


def test_opt_native_constant_expr():
    eq('native "1+1"', "2")
