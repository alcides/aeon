import sys
from typing import Annotated

from geneticengine.grammar.metahandlers.ints import IntRange
from sympy.core.numbers import Infinity
from sympy.logic.boolalg import to_dnf
from sympy.sets.sets import Interval
from sympy.simplify.simplify import simplify

from aeon.core.liquid import LiquidApp, LiquidVar, LiquidLiteralInt
from aeon.core.types import AbstractionType, BaseType, RefinedType, t_int, Top
from aeon.synthesis_grammar.bounds import refined_to_sympy_expression, sympy_exp_to_bounded_interval
from aeon.synthesis_grammar.grammar import (
    get_attribute_type_name,
    liquid_term_to_str,
    process_type_name,
    split_or_intervals,
    intervals_to_metahandlers,
)
from aeon.synthesis_grammar.utils import aeon_to_gengy_metahandlers


def test_abstract_type_name():
    abstract_ty = AbstractionType(
        "x", BaseType("Int"),
        AbstractionType("y", BaseType("Float"), BaseType("String")))
    assert get_attribute_type_name(abstract_ty) == "t_Int_t_Float_t_String"


# TODO more tests


def test_liquid_term_to_str():
    refined_ty = RefinedType(
        "g", t_int,
        LiquidApp(">", [LiquidVar("g"), LiquidLiteralInt(0)]))
    rt_str = liquid_term_to_str(refined_ty)
    assert rt_str == "Int_gt_0"
    refined_ty = RefinedType(
        "g",
        t_int,
        LiquidApp(
            "&&",
            [
                LiquidApp(
                    "||",
                    [
                        LiquidApp("<", [LiquidVar("g"),
                                        LiquidLiteralInt(0)]),
                        LiquidApp(">", [LiquidVar("g"),
                                        LiquidLiteralInt(10)]),
                    ],
                ),
                LiquidApp(
                    "||",
                    [
                        LiquidApp("<", [LiquidVar("g"),
                                        LiquidLiteralInt(20)]),
                        LiquidApp(">", [LiquidVar("g"),
                                        LiquidLiteralInt(30)]),
                    ],
                ),
            ],
        ),
    )
    rt_str = liquid_term_to_str(refined_ty)
    assert rt_str == "Int_lt_0_or_Int_gt_10_and_Int_lt_20_or_Int_gt_30"


def test_process_type_name():
    refined_ty = RefinedType(
        "g", t_int,
        LiquidApp(">", [LiquidVar("g"), LiquidLiteralInt(0)]))
    rt_str = process_type_name(refined_ty)
    assert rt_str == "Refined_Int_gt_0"
    refined_ty = RefinedType(
        "g",
        t_int,
        LiquidApp(
            "&&",
            [
                LiquidApp(
                    "||",
                    [
                        LiquidApp("<", [LiquidVar("g"),
                                        LiquidLiteralInt(0)]),
                        LiquidApp(">", [LiquidVar("g"),
                                        LiquidLiteralInt(10)]),
                    ],
                ),
                LiquidApp(
                    "||",
                    [
                        LiquidApp("<", [LiquidVar("g"),
                                        LiquidLiteralInt(20)]),
                        LiquidApp(">", [LiquidVar("g"),
                                        LiquidLiteralInt(30)]),
                    ],
                ),
            ],
        ),
    )
    rt_str = process_type_name(refined_ty)
    assert rt_str == "Refined_Int_lt_0_or_Int_gt_10_and_Int_lt_20_or_Int_gt_30"
    ty = BaseType("test")
    ty_str = process_type_name(ty)
    assert ty_str == "test"
    ty = Top()
    ty_str = process_type_name(ty)
    assert ty_str == "⊤"


def test_intervals_to_metahandlers():
    ty = RefinedType("g", t_int,
                     LiquidApp(
                         ">",
                         [LiquidVar("g"), LiquidLiteralInt(0)]))

    base_type_str = str(ty.type.name)
    gengy_metahandler = aeon_to_gengy_metahandlers[base_type_str]
    name, ref = ty.name, ty.refinement

    sympy_exp = refined_to_sympy_expression(ref)
    sympy_exp = simplify(sympy_exp)
    sympy_exp = to_dnf(sympy_exp)
    bounded_intervals = sympy_exp_to_bounded_interval(sympy_exp)
    intervals_list = split_or_intervals(bounded_intervals, name)
    assert len(intervals_list) == 1
    interval = intervals_list[0]
    assert isinstance(interval, Interval)
    assert isinstance(interval.sup, Infinity)
    assert interval.right_open
    assert interval.left_open

    metahandler_list = intervals_to_metahandlers(gengy_metahandler,
                                                 intervals_list, base_type_str,
                                                 ref)
    assert len(metahandler_list) == 1
    expected = Annotated[int, IntRange(1, sys.maxsize - 2)]
    assert str(metahandler_list[0]) == str(expected)
