from __future__ import annotations

from aeon.sugar.stypes import SBaseType
from tests.driver import check_compile


def test_anf():
    source = r"""
        type Unit;
        def math : Unit = native_import "math";
        def pow : (b: {c:Int | ((c >= 1)  && (c <= 100))}) -> (e:{d:Int | ((d >= 1) && (d <= 100))}) ->  Int = native "lambda x: lambda y: math.pow(x , y)";

"""
    check_compile(source, SBaseType("Top"))
