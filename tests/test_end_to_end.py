from aeon.frontend.parser import parse_term, parse_type
from aeon.backend.evaluator import EvaluationContext, eval
from aeon.core.types import top, t_int
from aeon.typing.typeinfer import check_type
from aeon.utils.ctx_helpers import build_context
from aeon.prelude.prelude import typing_vars, evaluation_vars

ctx = build_context(typing_vars)
ectx = EvaluationContext(evaluation_vars)


def check_compile(source, ty, res):
    p = parse_term(source)
    check_type(ctx, p, ty)
    assert eval(p, ectx) == res


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
    check_compile(source, parse_type("{x:Int | x == 1}"), 1)
