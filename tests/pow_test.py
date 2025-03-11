from __future__ import annotations

from aeon.sugar.stypes import SBaseType
from tests.driver import check_compile


def test_anf():
    source = r"""
        type Unit;
        def math : Unit = native_import "math";
        def pow : (b: {c:Int | ((c >= 1)  && (c <= 100))}) -> (e:{d:Int | ((d >= 1) && (d <= 100))}) -> Int = native "lambda x: lambda y: math.pow(x , y)";

"""
    check_compile(source, SBaseType("Top"))


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
    check_compile(source, SBaseType("Top"))
