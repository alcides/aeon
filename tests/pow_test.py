from __future__ import annotations

from aeon.sugar.desugar import desugar
from aeon.core.types import top
from aeon.sugar.parser import parse_program
from aeon.typechecking.typeinfer import check_type

def check_compile(source, ty, res):
    p, ctx, ectx = desugar(parse_program(source))
    assert check_type(ctx, p, ty)
    #assert eval(p, ectx) == res


def test_anf():
    source = r"""
        type Unit;
        def math : Unit = native_import "math";
        def pow : (b: {c:Int | ((c >= 1)  && (c <= 100))}) -> (e:{d:Int | ((d >= 1) && (d <= 100))}) ->  Int = native "lambda x: lambda y: math.pow(x , y)";

"""
    check_compile(source, top, 1)
