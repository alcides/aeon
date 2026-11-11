"""Array natives cannot invent element facts or bypass callback preconditions."""

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


def compile_source(source):
    driver = AeonDriver(AeonConfig("gp", SilentSynthesisUI(), 1))
    errors = list(driver.parse(aeon_code="import Array;\n" + source))
    return driver, errors


def test_head_cannot_prove_an_impossible_array_length():
    # Reduced from GP's four-element candidate accepted as a 50-item mask.
    _, errors = compile_source("""
        def main (u:Int):{a:(Array Bool) | Array.size a = 50} :=
            Array.mk_4 false false false (Array.head #[false]);
    """)
    assert errors, "Array.head must not introduce a false assumption that proves 4 = 50"


@pytest.mark.parametrize("element,accepted", [("false", False), ("true", True)])
def test_head_requires_its_promised_element_refinement(element, accepted):
    driver, errors = compile_source(f"def main (u:Int):{{v:Bool | v}} := Array.head #[{element}];")
    assert bool(errors) is not accepted
    if accepted:
        assert driver.run() is True


@pytest.mark.parametrize(
    "helpers,body,result_type,expected",
    [
        ("def f (x:{v:Int | v > 0}):Int := x;", "Array.map f #[ITEM]", "(Array Int)", [1]),
        ("def f (x:{v:Int | v > 0}):Bool := true;", "Array.filter f #[ITEM]", "(Array Int)", [1]),
        ("def f (x:{v:Int | v > 0}) (acc:Int):Int := x + acc;", "Array.reduce f 0 #[ITEM]", "Int", 1),
        ("def f (i:Int) (x:{v:Int | v > 0}):Int := x;", "Array.imap f #[ITEM]", "(Array Int)", [1]),
        ("def f (x:{v:Int | v > 0}) (y:Int):Int := x + y;", "Array.zipWith f #[ITEM] #[1]", "(Array Int)", [2]),
        ("def f (x:Int) (y:{v:Int | v > 0}):Int := x + y;", "Array.zipWith f #[1] #[ITEM]", "(Array Int)", [2]),
        ("def f (x:{v:Int | v > 0}):Bool := true;", "Array.count f #[ITEM]", "Int", 1),
    ],
)
@pytest.mark.parametrize("item,accepted", [("-1", False), ("1", True)])
def test_higher_order_array_operations_enforce_element_preconditions(
    helpers, body, result_type, expected, item, accepted
):
    driver, errors = compile_source(helpers + f"\ndef main (u:Int):{result_type} := {body.replace('ITEM', item)};")
    assert bool(errors) is not accepted
    if accepted:
        assert driver.run() == expected
