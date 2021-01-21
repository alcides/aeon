from aeon.typing.context import EmptyContext
from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt, LiquidVar
from aeon.typing.subtyping import is_subtype
from aeon.core.types import RefinedType, t_int
from aeon.frontend.parser import parse_type

rtrue = parse_type("{x:Int|true}")
x_eq_3 = parse_type("{x:Int| x == 3}")
y_eq_3 = parse_type("{y:Int| y == 3}")


def test_subtype1():
    assert is_subtype(EmptyContext(), rtrue, rtrue)


def test_subtype2():
    assert is_subtype(EmptyContext(), x_eq_3, x_eq_3)
    assert is_subtype(EmptyContext(), x_eq_3, y_eq_3)
