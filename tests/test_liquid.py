from aeon.core.liquid import LiquidLiteralInt, LiquidVar, LiquidApp
from aeon.core.substitutions import liquefy
from aeon.core.terms import Var, Literal, Application
from aeon.core.types import t_int
from aeon.utils.ast_helpers import i1

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
        "x", [LiquidLiteralInt(1)])
    assert LiquidApp("x", [LiquidLiteralInt(1)]) != LiquidApp(
        "x", [LiquidLiteralInt(2)])
    assert LiquidApp("x", [LiquidLiteralInt(1)]) != LiquidApp(
        "x", [LiquidVar("x2")])