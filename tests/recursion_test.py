from __future__ import annotations

from aeon.core.types import top
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.typechecking.typeinfer import check_type


def check_compile(source, ty, res):
    p, ctx, ectx = desugar(parse_program(source))
    assert check_type(ctx, p, ty)
    # assert eval(p, ectx) == res


def test_anf():
    source = r"""
        def gcd ( n:Int, z:Int) : Int {
            if z == 0 then n else (gcd(z)(n % z))
        }

        def main (x:Top) : Int {
            gcd 15 5
        }
"""
    check_compile(source, top, 1)
