from __future__ import annotations

from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidVar
from aeon.core.types import BaseType
from aeon.core.types import t_int
from aeon.sugar.stypes import SBaseType, SRefinedType
from aeon.verification.smt import smt_valid
from aeon.verification.vcs import Implication
from aeon.verification.vcs import LiquidConstraint
from tests.driver import check_compile, check_compile_expr
from aeon.sugar.parser import parse_expression

example = Implication(
    "x",
    t_int,
    LiquidApp("==", [LiquidVar("x"), LiquidLiteralInt(3)]),
    LiquidConstraint(
        LiquidApp(
            "==",
            [LiquidVar("x"), LiquidLiteralInt(3)],
        ),
    ),
)


def test_smt_example3():
    assert smt_valid(example)


example2 = Implication(
    "x",
    BaseType("a"),
    LiquidLiteralBool(True),
    Implication(
        "y",
        BaseType("a"),
        LiquidApp("==", [LiquidVar("x"), LiquidVar("y")]),
        LiquidConstraint(
            LiquidApp(
                "==",
                [LiquidVar("x"), LiquidVar("y")],
            ),
        ),
    ),
)


def test_other_sorts():
    assert smt_valid(example2)


def test_uninterpreted() -> None:
    aeon_code = """
type List;
def List_size: (l:List) -> Int = uninterpreted;

def List_new : {x:List | List_size x == 0} = native "[]" ;

def List_append (l:List) (i: Int) : {l2:List | List_size l2 == (List_size l) + 1} { native "l + [i]" }

def main (x:Int) : Unit {
    empty = List_new;
    one = List_append empty 3;
    print(one)
}"""
    check_compile(aeon_code, SBaseType("Top"))


def test_uninterpreted2() -> None:
    aeon_code = """
type List;
def List_size: (l:List) -> Int = uninterpreted;
def List_new : {u:List | List_size u == 0} = native "[]" ;
def List_append (l:List) (i: Int) : {l2:List | List_size l2 == List_size l + 1}  { native "l + [i]" }

def main (x:Int) : Unit {
    empty = List_new;
    one = List_append empty 3;
    print(one)
}"""
    check_compile(aeon_code, SBaseType("Top"))


def test_poly_to_smt():
    expected_stype = SRefinedType("y", SBaseType("Bool"), parse_expression("y == (x > (9 - z))"))

    assert check_compile_expr(
        "(x + z) > 9",
        expected_stype,
        extra_vars={
            "x": SBaseType("Int"),
            "z": SBaseType("Int"),
        },
    )
