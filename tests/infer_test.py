from __future__ import annotations

from aeon.core.types import t_int
from aeon.frontend.anf_converter import ensure_anf
from aeon.frontend.parser import parse_term
from aeon.frontend.parser import parse_type
from aeon.prelude.prelude import typing_vars
from aeon.typechecking import elaborate_and_check
from aeon.typechecking.context import EmptyContext
from aeon.typechecking.context import VariableBinder
from aeon.typechecking.entailment import entailment
from aeon.typechecking.typeinfer import sub
from aeon.utils.ctx_helpers import build_context


def tt(e: str, t: str, vars: None | dict[str, str] = None):
    base_dict = typing_vars.copy()
    if vars is not None:
        base_dict.update({k: parse_type(v) for (k, v) in vars.items()})

    ctx = build_context(base_dict)
    expected_type = parse_type(t)
    p = parse_term(e)
    core_ast_anf = ensure_anf(p)
    return elaborate_and_check(ctx, core_ast_anf, expected_type)


def test_one_is_int():
    assert tt("1", "Int")
    assert tt("1", "{x:Int|x == 1}")
    assert tt("1", "{x:Int|x > 0}")


def test_one_is_float():
    assert tt("1.0", "Float")
    assert tt("1.0", "{x:Float|x == 1.0}")
    assert tt("1.0", "{x:Float|x > 0}")


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
    assert tt("\\x -> x", "(x:Int) -> Int")
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
        "if x == 1 then 1 else 0",
        "{k:Int | (k == 1) || (k == 0) }",
        {"x": "Int"},
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


def test_sumSimple1():
    assert tt("if b then 0 else sum 0", "Int", {"b": "Bool", "sum": "(x:Int) -> Int"})


def test_sumSimple2():
    assert tt("let sum : (x: Int) -> Int = \\x -> sum x in sum 0", "Int")


def test_sumSimple3():
    assert tt(
        "let k = sum b in if k then 1 else 0",
        "Int",
        {"b": "Bool", "sum": "(x:Bool) -> Bool"},
    )


def test_sumSimple4():
    assert tt(
        "if sum b then 1 else 0",
        "Int",
        {"b": "Bool", "sum": "(x:Bool) -> Bool"},
    )


def test_sumSimple5():
    assert tt(
        r"let a : ((x:Int) -> Int) = \x -> a 1 in a 2",
        "Int",
        {"b": "Bool", "sum": "(x:Bool) -> Bool"},
    )


def test_sumToSimple4():
    assert tt("let k : {x:Int | x > 1} = 3 in k", "{k:Int| k > 0}")


def test_sumToSimple5():
    assert tt(
        "let k : (x:Int) -> {y:Int | y > x} = \\x -> x+1 in k 5",
        "{k:Int| k > 5}",
    )


def test_sumToSimple6():
    assert tt(
        "let k : (x:Int) -> {y:Int | y > 0} = \\x -> if x == 5 then k 1 else k 0 in k 5",
        "{k:Int| k > 0}",
    )


def test_sumTo():
    sumTo_def = """
        let sum : ((x: Int) -> {y: Int | (y >= 0) && (x <= y) }) =
        \\n ->
            let b : {k:Bool | k == (n <= 0)} = n <= 0 in
            if b then 0 else (
                let n_minus_1 : {nm1:Int | nm1 == (n - 1) } = (n - 1) in
                let sum_n_minus_1 : {s:Int| (s >= 0) && (n_minus_1 <= s)} = sum n_minus_1 in
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
    subt = parse_type(r"(x:(z:{a:Int| a > 1 }) -> Int) -> {k:Int | k > fresh_2}")
    supt = parse_type(r"(y:(m:{b:Int| b > 0 }) -> Int) -> {z:Int | z >= fresh_2}")
    c = sub(subt, supt)
    assert entailment(VariableBinder(EmptyContext(), "fresh_2", t_int), c)


def test_sub_simple():
    subt = parse_type(r"(_fresh_3:Int) -> Int")
    supt = parse_type(r"(y:Int) -> Int")

    c = sub(subt, supt)
    assert entailment(
        VariableBinder(EmptyContext(), "plus", parse_type("(x:Int) -> Int")),
        c,
    )


def test_capture_avoiding_subs():
    assert tt(
        "f1 (f2 3)",
        r"{k:Int | k >= 3 }",
        {
            "f1": r"(x:Int) -> {z:Int | z >= x}",
            "f2": r"(z:Int) -> {k:Int | k >= z}",
        },
    )


def test_max():
    max_type = "forall a:B, (x:a) -> (y:a) -> a"
    assert tt("let r = max[{x:Int | ?hole }] 0 5 in r + 1", "Int", {"max": max_type})
