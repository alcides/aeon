import pytest

from aeon.core.liquid import LiquidLiteralInt
from aeon.synthesis.modules.sygus.solver import _liquid_to_cvc5

cvc5 = pytest.importorskip("cvc5")


@pytest.mark.parametrize("value", [0, 2**31 - 1, 2**31, -(2**31), -(2**31) - 1, 2**63, 2**100, -(2**100)])
def test_integer_literal_translation_preserves_unbounded_values(value):
    solver = cvc5.Solver()
    result = _liquid_to_cvc5(LiquidLiteralInt(value), {}, solver, cvc5.Kind, False)
    assert result.getIntegerValue() == value
