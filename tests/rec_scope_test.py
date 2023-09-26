from __future__ import annotations

from aeon.backend.evaluator import eval
from aeon.core.types import top
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.typechecking.typeinfer import check_type


def check_compile(source, ty, res):
    p, ctx, ectx = desugar(parse_program(source))
    assert check_type(ctx, p, ty)
    assert eval(p, ectx) == res


def test_rec_scope():
    source = r"""
        def assert : (b:{b:Bool | b}) -> Unit = native "()";
        def main (args:Int) : Int {
            b = 3;
            1
        }
"""
    check_compile(source, top, 1)
