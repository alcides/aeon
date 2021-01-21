from aeon.frontend.parser import parse_type
from aeon.typing.context import EmptyContext
from aeon.typing.subtyping import is_subtype

rtrue = parse_type("{x:Int|true}")
x_eq_3 = parse_type("{x:Int| x == 3}")
y_eq_3 = parse_type("{y:Int| y == 3}")


def test_subtype1():
    assert is_subtype(EmptyContext(), rtrue, rtrue)


def test_subtype2():
    assert is_subtype(EmptyContext(), x_eq_3, x_eq_3)
    assert is_subtype(EmptyContext(), x_eq_3, y_eq_3)

    assert not is_subtype(EmptyContext(), parse_type("{x:Int|true}"),
                          parse_type("{x:Int|x == 2}"))

    assert is_subtype(EmptyContext(), parse_type("{x:Int|x > 1}"),
                      parse_type("{x:Int|x > 0}"))
