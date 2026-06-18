"""Division and modulo by a statically-zero divisor must be rejected.

The divisor parameter of ``/`` and ``%`` carries a ``{v | v != 0}`` refinement
(synthesised in ``aeon.typechecking.typeinfer.prim_op``), so the typechecker
demands a proof that the divisor is non-zero. A guard or a refinement that
bounds the divisor away from zero discharges the obligation.
"""

from aeon.facade.api import LiquidTypeCheckingFailedRelation
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SynthesisUI

setup_logger()


def _run(source: str):
    cfg = AeonConfig(synthesizer="none", synthesis_ui=SynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(cfg)
    errors = list(driver.parse(aeon_code=source))
    assert not errors, errors
    return driver.run()


def _errors(source: str):
    cfg = AeonConfig(synthesizer="none", synthesis_ui=SynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(cfg)
    return list(driver.parse(aeon_code=source))


def _rejected(source: str) -> bool:
    return any(isinstance(e, LiquidTypeCheckingFailedRelation) for e in _errors(source))


# --- accepted: the divisor is statically known to be non-zero ----------------


def test_int_division_by_literal_ok():
    assert _run("def main (args : Int) : Int := 10 / 2;") == 5


def test_int_modulo_by_literal_ok():
    assert _run("def main (args : Int) : Int := 10 % 3;") == 1


def test_float_division_by_literal_ok():
    assert _run("def main (args : Int) : Int := if 10.0 / 2.0 >= 1.0 then 0 else 1;") == 0


def test_int_division_guarded_ok():
    source = r"""
    def f (x : Int) (y : Int) : Int := if y != 0 then x / y else 0;
    def main (args : Int) : Int := f 10 0;
    """
    assert _run(source) == 0


def test_int_modulo_guarded_ok():
    source = r"""
    def f (x : Int) (y : Int) : Int := if y != 0 then x % y else 0;
    def main (args : Int) : Int := f 10 0;
    """
    assert _run(source) == 0


def test_float_division_guarded_ok():
    source = r"""
    def f (x : Float) (y : Float) : Float := if y != 0.0 then x / y else 0.0;
    def main (args : Int) : Int := if f 10.0 2.0 >= 1.0 then 0 else 1;
    """
    assert _run(source) == 0


def test_int_division_refinement_bounded_ok():
    source = r"""
    def f (x : Int) (y : {v : Int | v >= 1}) : Int := x / y;
    def main (args : Int) : Int := f 10 2;
    """
    assert _run(source) == 5


def test_float_division_refinement_bounded_ok():
    # A divisor refined away from zero (as in PSB2/bouncing_balls).
    source = r"""
    def f (x : Float) (y : {v : Float | 1.0 <= v && v <= 100.0}) : Float := x / y;
    def main (args : Int) : Int := if f 10.0 2.0 >= 1.0 then 0 else 1;
    """
    assert _run(source) == 0


# --- rejected: the divisor is not provably non-zero --------------------------


def test_int_division_unconstrained_divisor_rejected():
    source = r"""
    def f (x : Int) (y : Int) : Int := x / y;
    def main (args : Int) : Int := f 10 3;
    """
    assert _rejected(source)


def test_int_modulo_unconstrained_divisor_rejected():
    source = r"""
    def f (x : Int) (y : Int) : Int := x % y;
    def main (args : Int) : Int := f 10 3;
    """
    assert _rejected(source)


def test_float_division_unconstrained_divisor_rejected():
    source = r"""
    def f (x : Float) (y : Float) : Float := x / y;
    def main (args : Int) : Int := 0;
    """
    assert _rejected(source)


def test_int_division_by_literal_zero_rejected():
    source = r"""
    def f (x : Int) : Int := x / 0;
    def main (args : Int) : Int := f 5;
    """
    assert _rejected(source)


def test_int_modulo_by_literal_zero_rejected():
    source = r"""
    def f (x : Int) : Int := x % 0;
    def main (args : Int) : Int := f 5;
    """
    assert _rejected(source)


def test_both_operands_literal_division_rejected():
    # Both operands constant: the constant ``5 / 0`` reaches the SMT layer and
    # is caught rather than silently skipped (smt.smt_valid ZeroDivisionError).
    assert _rejected("def main (args : Int) : Int := 5 / 0;")


def test_both_operands_literal_modulo_rejected():
    assert _rejected("def main (args : Int) : Int := 5 % 0;")
