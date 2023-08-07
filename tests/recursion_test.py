from __future__ import annotations

from aeon.core.types import top
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.typechecking.typeinfer import check_type
from aeon.typechecking.elaboration import elaborate


def check_compile(source, ty):
    p, ctx, ectx = desugar(parse_program(source))
    p2 = elaborate(ctx, p)
    assert check_type(ctx, p2, ty)


def test_anf():
    source = r"""
        def gcd ( n:Int) (z:Int) : Int {
            if z == 0 then n else (gcd(z)(n % z))
        }

        def main (x:Top) : Int {
            gcd 15 5
        }
"""
    check_compile(source, top)
