from __future__ import annotations

from aeon.core.types import top
from aeon.frontend.anf_converter import ensure_anf
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.typechecking import elaborate_and_check


def check_compile(source, ty):
    p, ctx, ectx, _ = desugar(parse_program(source))
    core_ast_anf = ensure_anf(p)
    assert elaborate_and_check(ctx, core_ast_anf, ty)


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
