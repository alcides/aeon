from aeon.typing.context import EmptyContext, VariableBinder
from typing import Dict

from aeon.typing.typeinfer import check_type
from aeon.frontend.parser import parse_type, parse_term

from aeon.utils.ctx_helpers import build_context
from aeon.typing.typeinfer import sub
from aeon.verification.smt import smt_valid
from aeon.typing.entailment import entailment
from aeon.core.types import t_int


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


def test_negatives():
    assert not tt("1", "{x:Int| x == 0}")
    assert not tt("2", "{x:Int| x >= 5}")
    assert tt("5-2", "{x:Int| x == 3}")
    assert tt("0-2", "{x:Int| x == (-2)}")
    assert tt("0-2", "{x:Int| x <= 0}")
    assert not tt("0-2", "{x:Int| x == (0-1)}")


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
    assert tt(
        "if x == 1 then 1 else 0", "{k:Int | (k == 1) || (k == 0) }", {"x": "Int"}
    )
    assert not tt("if x then 1 else 0", "Int", {"x": "Int"})


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


def test_abs_f():
    assert tt("let f : (x:Int) -> Int = \\x -> x in f 1", "Int")


def test_abs_if():
    assert not tt("let f : (x:Int) -> Int = \\x -> x in if f 1 then 0 else 0", "Int")
    assert tt("let f : (x:Int) -> Bool = \\x -> true in if f 1 then 0 else 0", "Int")


def test_sumSimple():
    assert tt("if b then 0 else sum 0", "Int", {"b": "Bool", "sum": "(x:Int) -> Int"})
    assert tt("let sum : (x: Int) -> Int = \\x -> sum x in sum 0", "Int")
    assert tt(
        "let k = sum b in if k then 1 else 0",
        "Int",
        {"b": "Bool", "sum": "(x:Bool) -> Bool"},
    )


def test_sumSimple2():
    assert tt(
        "if sum b then 1 else 0",
        "Int",
        {"b": "Bool", "sum": "(x:Bool) -> Bool"},
    )


def test_sumSimple3():
    assert tt(
        r"let a : ((x:Int) -> Int) = \x -> a 1 in a 2",
        "Int",
        {"b": "Bool", "sum": "(x:Bool) -> Bool"},
    )


def test_sumToSimple4():
    assert tt("let k : {x:Int | x > 1} = 3 in k", "{k:Int| k > 0}")

    assert tt(
        "let k : (x:Int) -> {y:Int | y > x} = \\x -> x+1 in k 5", "{k:Int| k > 5}"
    )

    assert tt(
        "let k : (x:Int) -> {y:Int | y > 0} = \\x -> if x == 5 then k 1 else k 0 in k 5",
        "{k:Int| k > 0}",
    )


def test_sumTo():
    sumTo_def = """
        let sum : ((x: Int) -> {y: Int | (y >= 0) && (x <= y) }) =
        \\n -> 
            let b : {k:Bool | n <= 0} = n <= 0 in
            if b then 0 else (
                let n_minus_1 : {nm1:Int | nm1 == (n - 1) } = (n - 1) in
                let sum_n_minus_1 : {s:Int| (s >= 0) && (s <= n_minus_1)} = sum n_minus_1 in
                n + sum_n_minus_1
            ) in 1
    """
    sumTo_type = "Int"
    assert tt(sumTo_def, sumTo_type)
    """
    sumTo_def = "let sum : ((x: Int) -> {y: Int | (y >= 0) && (x <= y) }) = \\n -> if n <= 0 then 0 else n + sum (n-1) in sum"
    sumTo_type = "(x: Int) -> {y: Int | (y >= 0) && (x <= y) } "
    """


def test_simplerec():
    assert tt("let x : Int = 1 in x", "Int")


def test_let_let():
    assert tt("let x = let y = 1 in 1 in 2", "Int")


def test_sub():
    subt = parse_type(r"(x:((z:{a:Int| a > 1 }) -> Int)) -> {k:Int | k > x}")
    supt = parse_type(r"(y:((m:{b:Int| b > 0 }) -> Int)) -> {z:Int | z >= y}")
    c = sub(subt, supt)
    assert entailment(VariableBinder(EmptyContext(), "fresh_2", t_int), c)


def test_sub_simple():
    subt = parse_type(r"(_fresh_3:Int) -> Int")
    supt = parse_type(r"(y:Int) -> Int")

    c = sub(subt, supt)
    assert entailment(
        VariableBinder(EmptyContext(), "plus", parse_type("(x:Int) -> Int")), c
    )


"ø,plus:(x:Int) -> Int (x:Int) -> Int (fresh_1:Int) -> Int"
