"""Array transforms retain the predicate checked by subsequent reads."""

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


@pytest.mark.parametrize(
    "expression,accepted,value",
    [
        ("Array.reversed #[1,2]", True, 2),
        ("Array.set #[1,2] 0 3", True, 3),
        ("Array.reversed #[-1,-2]", False, None),
        ("Array.set #[1,2] 0 (-3)", False, None),
        ("Array.set #[-1,-2] 0 3", False, None),
    ],
)
def test_transform_preserves_only_supported_element_facts(expression, accepted, value):
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0))
    errors = list(
        driver.parse(
            aeon_code=f"""
        import Array;
        def main (_:Int):{{v:Int | v > 0}} := Array.head ({expression});
    """
        )
    )
    assert bool(errors) is not accepted
    if accepted:
        assert driver.run() == value


def test_transform_preserves_both_length_and_element_predicate():
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0))
    errors = list(
        driver.parse(
            aeon_code="""
        import Array;
        def transform (1 arr:{a:(Array {v:Int | v > 0}) | Array.size a = 2}):
            {a:(Array {v:Int | v > 0}) | Array.size a = 2} :=
            Array.reversed (Array.set arr 1 3);
        def main (_:Int):Int := (Array.consume Array.sum) (transform #[1,2]);
    """
        )
    )
    assert not errors, errors
    assert driver.run() == 4
