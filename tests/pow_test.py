from __future__ import annotations

from aeon.sugar.desugar import desugar
from aeon.core.types import top
from aeon.sugar.parser import parse_program
from aeon.typechecking import elaborate_and_check


def check_compile(source, ty):
    p, ctx, ectx, _ = desugar(parse_program(source))
    assert elaborate_and_check(ctx, p, ty)


def test_anf():
    source = r"""
        type Unit;
        def math : Unit = native_import "math";
        def pow : (b: {c:Int | ((c >= 1)  && (c <= 100))}) -> (e:{d:Int | ((d >= 1) && (d <= 100))}) ->  Int = native "lambda x: lambda y: math.pow(x , y)";

"""
    check_compile(source, top)
