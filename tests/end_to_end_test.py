from __future__ import annotations

from aeon.backend.evaluator import eval
from aeon.backend.evaluator import EvaluationContext
from aeon.core.types import top
from aeon.frontend.parser import parse_term
from aeon.frontend.parser import parse_type
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.prelude.prelude import evaluation_vars
from aeon.prelude.prelude import typing_vars
from aeon.typechecking.elaboration import elaborate
from aeon.typechecking.typeinfer import check_type
from aeon.utils.ctx_helpers import build_context

ctx = build_context(typing_vars)
ectx = EvaluationContext(evaluation_vars)


def check_compile(source, ty, res):
    p = parse_term(source)
    p2 = elaborate(ctx, p)
    assert check_type(ctx, p2, ty)
    assert eval(p2, ectx) == res


def check_sugar(source, ty, res):
    p = parse_program(source)
    p, ctx, ectx = desugar(p)
    p2 = elaborate(ctx, p)
    assert check_type(ctx, p2, ty)
    assert eval(p2, ectx) == res


def test_anf():
    source = r"""let f : (x:Int) -> (y:Int) -> Int = (\x -> (\y -> x)) in
           let r = f (f 1 2) (f 2 3) in
           r"""
    check_compile(source, top, 1)


def test_anf_typed():
    source = r"""let f : (x:Int) -> (y:Int) -> {z:Int | z == x } = (\x -> (\y -> x)) in
           let r = f (f 1 2) (f 2 3) in
           r"""
    check_compile(source, top, 1)


def test_anf_typed_smaller():
    source = r"""let f : (x:Int) -> (y:Int) -> {z:Int | z == x } = (\x -> (\y -> x)) in
           f (f 3 4) 2"""
    check_compile(source, parse_type("{x:Int | x == 3}"), 3)


def test_annotation():
    source = r""" (1 : Int) """
    check_compile(source, parse_type("Int"), 1)


def test_annotation_anf():
    source = r"""let j = (let f : (x:Int) -> {y :Int | y == x} = \x -> x in let a : {x:Int | x == 3} = 3 in f a) in j"""
    check_compile(source, parse_type("{x:Int | x == 3}"), 3)


def test_annotation_anf2():
    source = r"""let j : {x:Int | x == 3} = (let f : (x:Int) -> {y :Int | y == x} = \x -> x in let a : {x:Int | x == 3} = (let k : {x:Int | x == 3} = 3 in k) in f a) in j"""
    check_compile(source, parse_type("{x:Int | x == 3}"), 3)


def test_double_forall():
    source = r"""
    type Tuple x:B,y:B;
    def fun : forall a:B, forall b:B, (x:a) -> (y:b) -> Tuple [a, b] = native "lambda x: lambda y: (x,y)";
    def r : Tuple [Int, Float] = fun 3 3.0; def main : Top = r; """
    expected_type = parse_type("Tuple [Int, Float]")
    check_sugar(source, expected_type, (3, 3.0))
