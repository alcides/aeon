from __future__ import annotations

from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidVar
from aeon.core.substitutions import liquefy
from aeon.core.terms import Application
from aeon.core.terms import Var
from aeon.sugar.stypes import SBaseType
from aeon.utils.ast_helpers import i1
from tests.driver import check_compile

l1 = LiquidLiteralInt(1)
lx = LiquidVar("x")
lx1 = LiquidApp("x", [l1])
x = Var("x")
x1 = Application(x, i1)


def test_liquefaction():
    assert liquefy(x) == lx
    assert liquefy(i1) == l1
    assert liquefy(x1) == lx1


def test_simple_eq():
    assert LiquidApp("x", [LiquidLiteralInt(1)]) == LiquidApp(
        "x",
        [LiquidLiteralInt(1)],
    )
    assert LiquidApp("x", [LiquidLiteralInt(1)]) != LiquidApp(
        "x",
        [LiquidLiteralInt(2)],
    )
    assert LiquidApp("x", [LiquidLiteralInt(1)]) != LiquidApp(
        "x", [LiquidVar("x2")])


def test_liquid_types_syntax():
    source = r"""
        def test (n:Int | n > 0) (z:Int) : Int {
            n + z
        }

        def main (x:Int) : Unit {
            print(test 5 5)
        }
"""
    check_compile(source, SBaseType("Top"), 0)
