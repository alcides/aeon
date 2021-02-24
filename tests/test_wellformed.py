from aeon.core.liquid import LiquidLiteralBool
from aeon.core.types import BaseType, RefinedType, AbstractionType, t_int, t_bool
from aeon.typing.context import TypingContext, EmptyContext, VariableBinder
from aeon.typing.well_formed import wellformed
from aeon.frontend.parser import parse_type

empty = EmptyContext()


def test_wf1():
    assert wellformed(empty, t_int)
    assert wellformed(empty, t_bool)
    assert wellformed(empty, BaseType("A"))


def test_wf2():
    assert wellformed(empty, parse_type("(x:Int) -> Int"))
    assert wellformed(empty, parse_type("(x:Int) -> Bool"))
    assert wellformed(empty, parse_type("(x:Int) -> (y:Bool) -> Bool"))
    assert wellformed(empty, parse_type("(x:((y:Int) -> Bool)) -> (y:Bool) -> Bool"))


def test_refined():
    assert wellformed(empty, parse_type("{x:Int | true}"))
    assert wellformed(empty, parse_type("{x:Int | false}"))
    assert wellformed(empty, parse_type("{x:Bool | x }"))
    assert wellformed(empty, parse_type("{x:Bool | x == false }"))
    assert wellformed(empty, parse_type("{x:Int | x > 0}"))


def test_dependent():
    assert wellformed(empty, parse_type("(y:Int) -> {x:Int | x > y}"))
    assert wellformed(
        VariableBinder(empty, "x", t_int), parse_type("(y:Int) -> {z:Int | x > y}")
    )
