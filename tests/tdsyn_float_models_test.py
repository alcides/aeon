"""SMT literals retain the precision of Python Float values."""

from fractions import Fraction
from math import sqrt

import pytest
import z3

from aeon.compilation.session import CompilationSession
from aeon.core.parser import parse_type
from aeon.synthesis.modules.tdsyn.smt_solve import _model_float, literal_satisfies, solve_literals
from aeon.synthesis.modules.tdsyn.worklist import fresh_hole
from aeon.typechecking.context import TypingContext


@pytest.mark.parametrize(
    "value", ["0.000000000005", "-0.000000000005", "1.234567891234567", "1e-300", "1e300", "5e-324"]
)
def test_rational_conversion_has_no_fixed_decimal_cutoff(value):
    exact = Fraction(value)
    numeral = z3.RealVal(f"{exact.numerator}/{exact.denominator}")
    assert _model_float(numeral) == float(exact)


def test_large_numerator_and_denominator_do_not_overflow_individually():
    numerator = 10**500 + 1
    assert _model_float(z3.RealVal(f"{numerator}/{10**500}")) == 1.0


@pytest.mark.parametrize("sign", [1, -1])
def test_algebraic_conversion_uses_binary_float_precision(sign):
    x = z3.Real("x")
    solver = z3.Solver()
    solver.add(x * x == 2, sign * x > 0)
    assert solver.check() == z3.sat
    assert _model_float(solver.model()[x]) == sign * sqrt(2)


def test_small_positive_models_still_satisfy_the_goal():
    with CompilationSession().activate():
        ty = parse_type("{v:Float | v > 0.0 && v < 0.00000000001}")
        _, hole = fresh_hole(ty, TypingContext())
        solutions = solve_literals([hole])
        assert solutions
        assert all(literal_satisfies(solution[hole.name], ty) for solution in solutions)
