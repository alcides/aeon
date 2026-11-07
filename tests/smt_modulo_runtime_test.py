"""Existential witnesses must use the interpreter's signed-remainder semantics."""

import pytest
import z3

from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
from aeon.utils.name import Name
from aeon.verification.smt import base_functions, translate_liq
from aeon.backend.liquid_eval import eval_liquid
from aeon.backend.python_export import gen
from aeon.core.terms import Application, Literal, Var
from aeon.core.types import t_int
from aeon.prelude.prelude import evaluation_vars


@pytest.mark.parametrize("dividend", [-5, 0, 5])
@pytest.mark.parametrize("divisor", [-4, -1, 1, 4])
def test_modulo_translation_matches_runtime(dividend, divisor):
    expression = LiquidApp(Name("%"), [LiquidLiteralInt(dividend), LiquidLiteralInt(divisor)])
    assert z3.simplify(translate_liq(expression, base_functions)).as_long() == dividend % divisor


@pytest.mark.parametrize("operator", ["/", "%"])
@pytest.mark.parametrize("dividend", [-7, 0, 7, 10**30 + 1])
@pytest.mark.parametrize("divisor", [-8, -3, 3, 8])
def test_integer_quotient_and_remainder_agree_across_backends(operator, dividend, divisor):
    expected = dividend // divisor if operator == "/" else dividend % divisor
    name = Name(operator, 0)
    liquid = LiquidApp(name, [LiquidLiteralInt(dividend), LiquidLiteralInt(divisor)])
    assert z3.simplify(translate_liq(liquid, base_functions)).as_long() == expected
    assert eval_liquid(liquid, {}, uninterpreted={}, runtime={}) == expected
    runtime = evaluation_vars[name](dividend)(divisor)
    assert type(runtime) is int and runtime == expected
    term = Application(Application(Var(name), Literal(dividend, t_int)), Literal(divisor, t_int))
    assert eval(gen(term)) == expected


def test_float_division_remains_fractional():
    assert evaluation_vars[Name("/", 0)](7.0)(8.0) == 0.875
    expression = base_functions["/"](z3.RealVal(7), z3.RealVal(-8))
    assert z3.simplify(expression == z3.RealVal("-0.875")) == z3.BoolVal(True)


def test_symbolic_modulo_rejects_incorrect_positive_remainder():
    x, y = Name("x"), Name("y")
    zx, zy = z3.Ints("x y")
    expression = LiquidApp(Name("%"), [LiquidVar(x), LiquidVar(y)])
    solver = z3.Solver()
    solver.add(zx == 5, zy == -4, translate_liq(expression, {str(x): zx, str(y): zy}) >= 0)
    assert solver.check() == z3.unsat
