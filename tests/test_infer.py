from typing import Dict

from aeon.typing.typeinfer import check_type
from aeon.frontend.parser import parse_type, parse_term

from aeon.utils.ctx_helpers import build_context


def tt(e: str, t: str, vars: Dict[str, str] = {}):
    ctx = build_context({k: parse_type(v) for (k, v) in vars.items()})
    return check_type(ctx, parse_term(e), parse_type(t))


def test_one_is_int():
    assert tt("1", "Int")
    assert tt("1", "{x:Int|x == 1}")
    assert tt("1", "{x:Int|x > 0}")


def test_true_is_bool():
    assert tt("true", "Bool")
    assert tt("true", "{x:Bool|x == true}")
    assert tt("true", "{x:Bool|x}")


def test_a_is_bool():
    assert tt("a", "Bool", {"a": "Bool"})
    assert tt("a", "Bool", {"a": "{x:Bool| x == true}"})
    assert tt("a", "{x:Bool| x == true}", {"a": "{x:Bool| x == true}"})


def test_a_is_not_bool():
    assert not tt("a", "Bool", {"a": "Int"})
    assert not tt("a", "Int", {"a": "{x:Bool| x == true}"})
    assert not tt("a", "Bool", {"a": "{x:Int| x > 0}"})
    assert not tt("a", "{x:Bool| x == false}", {"a": "{x:Bool| x == true}"})


def test_abs_is_int():
    # assert tt("\\x -> x", "(x:Int) -> Int")
    assert not tt("\\x -> x", "(x:Bool) -> Int")


# lambda

nat = "{v:Int | 0 <= v}"
pos = "{v:Int | 0 < v}"


def test_six():
    assert tt("6", nat)


def test_nine():
    assert tt("6+3", nat)


def test_two():
    assert tt("let a = 1 in 2", "Int")


def test_fifteen():
    fifteen = "let six = 6 in let nine = 9 in 6 + 9"
    assert tt(fifteen, nat)


# Branches


def test_if():
    assert tt("if x == 1 then 1 else 0", "Int", {"x": "Int"})
    assert tt("if x == 1 then 1 else 0", "{k:Int | (k == 1) || (k == 0) }",
              {"x": "Int"})


def test_not():
    not_def = "\\x -> if x then false else true"
    not_type = "(x:Bool) -> {b:Bool | b == !x}"
    assert tt(not_def, not_type)


def test_and():
    and_def = "\\x -> \\y -> if x then y else false"
    and_type = "(x:Bool) -> (y:Bool) -> {z:Bool | z == (x && y)}"
    assert tt(and_def, and_type)


def test_or():
    or_def = "\\x -> \\y -> if x then true else y"
    or_type = "(x:Bool) -> (y:Bool) -> {z:Bool | z == (x || y)}"
    assert tt(or_def, or_type)


# Selfication


def test_abs():
    abs_def = "\\x -> if x >= 0 then x else -x"
    abs_type = "(x:Int) -> {z:Int | z >= 0}"
    assert tt(abs_def, abs_type)


def test_sumTo():
    sumTo_def = "let sum : ((x: Int) -> {y: Int | (y >= 0) && (x <= y) }) = \\n -> if n < 0 then 0 else n + (sum (n - 1)) in sum"
    sumTo_type = "(x: Int) -> {y: Int | (y >= 0) && (x <= y) } "
    assert tt(sumTo_def, sumTo_type)
