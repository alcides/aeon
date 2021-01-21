from aeon.typing.context import EmptyContext
from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt, LiquidVar
from aeon.typing.subtyping import is_subtype
from aeon.core.types import RefinedType, t_int

rtrue = RefinedType("x", t_int, LiquidLiteralBool(True))

x_eq_3 = RefinedType(
    "x", t_int, LiquidApp("eq",
                          [LiquidVar("x"), LiquidLiteralInt(3)]))
y_eq_3 = RefinedType(
    "y", t_int, LiquidApp("eq",
                          [LiquidVar("y"), LiquidLiteralInt(3)]))


def test_subtype1():
    assert is_subtype(EmptyContext(), rtrue, rtrue)


def test_subtype2():
    assert is_subtype(EmptyContext(), x_eq_3, x_eq_3)
    assert is_subtype(EmptyContext(), x_eq_3, y_eq_3)
