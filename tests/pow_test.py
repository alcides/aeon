from __future__ import annotations

from tests.driver import check_compile
from aeon.sugar.ast_helpers import st_top


def test_anf():
    source = r"""
        def math : Unit = native_import "math";
        def pow (x: {c:Int | ((c >= 1) && (c <= 100))}) (y:{d:Int | ((d >= 1) && (d <= 100))}) : Int { native "math.pow(x, y)" }

"""
    check_compile(source, st_top)


def test_abs():
    source = r"""
        def abs (x: Int) : {k:Int | ?h} {
            if x > 0 then x else (0-x)
        }

        def main (x: Int) : Int {
            let k : {x:Int | x > 0} = abs (-3);
            1
        }
"""
    check_compile(source, st_top)
