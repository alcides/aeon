from __future__ import annotations

from aeon.backend.evaluator import eval
from aeon.core.types import top
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.typechecking import elaborate_and_check


def check_compile(source, ty):
    p, ctx, ectx, _ = desugar(parse_program(source))
    assert elaborate_and_check(ctx, p, ty)
    assert eval(p, ectx) == 2


def test_anf_native():
    source = r"""
        type Unit;
        def plus1 : (i:Int) -> Int = \i -> i + 1;
        def test_native : (i:Int) -> Int = native "lambda x: plus1(x)";
        def main (i:Int) : Int {  test_native 1}
"""
    check_compile(source, top)
