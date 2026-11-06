"""Existential witnesses must use the interpreter's signed-remainder semantics."""

import pytest
import z3

from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
from aeon.utils.name import Name
from aeon.verification.smt import base_functions, translate_liq


@pytest.mark.parametrize("dividend", [-5, 0, 5])
@pytest.mark.parametrize("divisor", [-4, -1, 1, 4])
def test_modulo_translation_matches_runtime(dividend, divisor):
    expression = LiquidApp(Name("%"), [LiquidLiteralInt(dividend), LiquidLiteralInt(divisor)])
    assert z3.simplify(translate_liq(expression, base_functions)).as_long() == dividend % divisor


def test_symbolic_modulo_rejects_incorrect_positive_remainder():
    x, y = Name("x"), Name("y")
    zx, zy = z3.Ints("x y")
    expression = LiquidApp(Name("%"), [LiquidVar(x), LiquidVar(y)])
    solver = z3.Solver()
    solver.add(zx == 5, zy == -4, translate_liq(expression, {str(x): zx, str(y): zy}) >= 0)
    assert solver.check() == z3.unsat
