"""Array.head's non-empty precondition must hold even inside a guard."""

import pytest

from aeon.errors import LiquidTypeCheckingFailedRelation
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


def _compile(expression: str):
    driver = AeonDriver(AeonConfig("gp", SilentSynthesisUI(), 0))
    errors = list(driver.parse(aeon_code=f"open Array; def main (_:Int):Int := {expression};"))
    return driver, errors


@pytest.mark.parametrize(
    "expression",
    [
        "head (mk_empty unit)",
        "head (mk_repeat 0 7)",
        "head (mk_concat (mk_empty unit) (mk_empty unit))",
        "if head (mk_empty unit) = true then 1 else 2",
        "if head (mk_concat (mk_empty unit) (mk_empty unit)) = true then 1 else 2",
        "if head (mk_empty unit) = (get (mk_empty unit) 8 != 1.0) then 1 else 2",
    ],
)
def test_head_rejects_empty_arrays(expression):
    _, errors = _compile(expression)
    assert any(isinstance(error, LiquidTypeCheckingFailedRelation) for error in errors), errors


@pytest.mark.parametrize(
    "expression, expected",
    [
        ("head (mk_1 7)", 7),
        ("head (mk_repeat 3 7)", 7),
        ("head (mk_concat (mk_empty unit) (mk_2 7 8))", 7),
        ("if head (mk_1 true) = true then 1 else 2", 1),
    ],
)
def test_head_accepts_nonempty_arrays(expression, expected):
    driver, errors = _compile(expression)
    assert not errors, errors
    assert driver.run() == expected


def test_head_preserves_element_refinement():
    driver = AeonDriver(AeonConfig("gp", SilentSynthesisUI(), 0))
    errors = list(
        driver.parse(
            aeon_code="""
open Array;
def main (_:Int):{n:Int | n > 0} := head (mk_repeat 3 7);
"""
        )
    )
    assert not errors, errors
    assert driver.run() == 7


def test_head_cannot_invent_an_element_refinement():
    driver = AeonDriver(AeonConfig("gp", SilentSynthesisUI(), 0))
    errors = list(
        driver.parse(
            aeon_code="""
open Array;
def main (_:Int):{n:Int | n < 0} := head (mk_1 7);
"""
        )
    )
    assert any(isinstance(error, LiquidTypeCheckingFailedRelation) for error in errors), errors
