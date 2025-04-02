from aeon.utils.name import Name
from aeon.frontend.parser import parse_type
from aeon.typechecking.context import TypingContext, VariableBinder
from aeon.typechecking.entailment import entailment
from aeon.verification.sub import sub
from aeon.core.types import t_int


def test_sub():
    subt = parse_type(r"(x:(z:{a:Int| a > 1 }) -> Int) -> {k:Int | k > fresh_2}")
    supt = parse_type(r"(y:(m:{b:Int| b > 0 }) -> Int) -> {z:Int | z >= fresh_2}")
    c = sub(TypingContext(), subt, supt)
    assert entailment(TypingContext([VariableBinder(Name("fresh_2"), t_int)]), c)


def test_sub_simple():
    subt = parse_type(r"(_fresh_3:Int) -> Int")
    supt = parse_type(r"(y:Int) -> Int")

    c = sub(TypingContext(), subt, supt)
    assert entailment(
        TypingContext([VariableBinder(Name("plus", 0), parse_type("(x:Int) -> Int"))]),
        c,
    )
