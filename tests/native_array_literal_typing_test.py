"""Native solver arrays keep their real constructor and prove element/size types."""

import pytest

from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
from aeon.core.terms import Literal
from aeon.core.types import RefinedType, TypeConstructor, t_int, top
from aeon.synthesis.identification import get_holes_info, incomplete_functions_and_holes
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name
from tests.joint_hole_synthesis_test import parse


def array_type(element="Int", length=2):
    driver = parse(f"import Array; def value(_:Unit):{{a:(Array {element}) | Array.size a = {length}}} := ?h;")
    targets = incomplete_functions_and_holes(driver.typing_ctx, driver.core)
    ty, ctx = get_holes_info(driver.typing_ctx, driver.core, top, targets, refined_types=True)[targets[0][1][0]]
    return ctx, ty


@pytest.mark.parametrize("element,values", [("Int", [1, 2]), ("Float", [1.0, 2.0]), ("Bool", [True, False])])
def test_native_arrays_prove_the_declared_length(element, values):
    ctx, ty = array_type(element)
    assert check_type(ctx, Literal(values, ty.type), ty)
    assert not check_type(ctx, Literal(values[:1], ty.type), ty)


@pytest.mark.parametrize("values", [[True, False], [1.0, 2.0], [1, "wrong"], [object(), object()], (1, 2)])
def test_native_arrays_cannot_cast_malformed_elements(values):
    ctx, ty = array_type()
    assert not check_type(ctx, Literal(values, ty.type), ty)


def test_array_element_refinements_are_checked_for_every_element():
    ctx, ty = array_type()
    value = Name("element", 0)
    positive = RefinedType(value, t_int, LiquidApp(Name(">", 0), [LiquidVar(value), LiquidLiteralInt(0)]))
    base = TypeConstructor(ty.type.name, [positive])
    assert check_type(ctx, Literal([1, 2], base), base)
    assert not check_type(ctx, Literal([1, -2], base), base)


def test_nested_native_array_elements_are_checked_recursively():
    ctx, ty = array_type("(Array Int)")
    assert check_type(ctx, Literal([[1], [2, 3]], ty.type), ty)
    assert not check_type(ctx, Literal([[1], [True]], ty.type), ty)


def test_unbound_lookalike_array_constructor_is_not_a_cast():
    ctx, ty = array_type()
    assert not check_type(ctx, Literal([1, 2], TypeConstructor(Name("Array", 0), [t_int])), ty)
