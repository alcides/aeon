"""Preconditions are checked before execution; false parameters only warn."""

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.verification.preconditions import RefinementPreconditionError


def compile_source(tmp_path, source, **options):
    path = tmp_path / "preconditions.ae"
    path.write_text(source)
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 0, no_main=True, **options))
    return driver, list(driver.parse(filename=str(path), aeon_code=source))


@pytest.mark.parametrize("argument", ["0 - 1", "0"])
def test_closed_refinement_call_checks_precondition(tmp_path, argument):
    _, errors = compile_source(
        tmp_path,
        f"""
    def positive (x:{{x:Int | x > 0}}) : {{r:Int | r > 0}} := x;
    def wrong : {{p:Unit | positive ({argument}) > 0}} := unit;
    """,
    )
    assert any(isinstance(e, RefinementPreconditionError) for e in errors)


def test_symbolic_call_cannot_assume_its_own_result(tmp_path):
    _, errors = compile_source(
        tmp_path,
        """
    def positive (x:{x:Int | x > 0}):Int := x;
    def wrong (n:Int):{p:Unit | positive n > 0} := unit;
    """,
    )
    assert any(isinstance(e, RefinementPreconditionError) for e in errors)


@pytest.mark.parametrize("argument", ["1", "n"])
def test_valid_precondition(tmp_path, argument):
    _, errors = compile_source(
        tmp_path,
        f"""
    def positive (x:{{x:Int | x > 0}}):{{r:Int | r > 0}} := x;
    def valid (n:{{v:Int | v > 0}}):{{p:Unit | positive {argument} > 0}} := unit;
    """,
    )
    assert not errors


def test_runtime_call_rejected(tmp_path):
    _, errors = compile_source(
        tmp_path,
        """
    def positive (x:{x:Int | x > 0}):Int := x;
    def wrong : Int := positive (0 - 1);
    """,
    )
    assert errors


@pytest.mark.parametrize("predicate", ["false", "1 > 2"])
def test_false_parameter_warns_without_error(tmp_path, predicate):
    driver, errors = compile_source(tmp_path, f"def f (x:{{x:Int | {predicate}}}):Int := x;", strict_decidable=True)
    assert not errors
    assert len(driver.false_parameter_warnings) == 1
    assert "Parameter 'x'" in driver.false_parameter_warnings[0].message


def test_boolean_false_is_not_an_impossible_parameter(tmp_path):
    driver, errors = compile_source(tmp_path, "def f (x:{x:Bool | x = false}):Bool := x;")
    assert not errors
    assert not driver.false_parameter_warnings


def test_call_inside_higher_order_refinement_checks_precondition(tmp_path):
    _, errors = compile_source(
        tmp_path,
        """import List;
    def positive (x:{x:Int | x > 0}):Int := x;
    def wrong : {p:Unit | List.all (fun x => positive (0 - 1) > 0) [1]} := unit;
    """,
    )
    assert any(isinstance(e, RefinementPreconditionError) for e in errors), errors


def test_false_parameter_warning_is_printed_even_in_strict_mode(tmp_path, capsys):
    from aeon.__main__ import print_decidability_warnings

    driver, errors = compile_source(tmp_path, "def f (x:{x:Int | false}):Int := x;", strict_decidable=True)
    assert not errors
    print_decidability_warnings(driver)
    output = capsys.readouterr().err
    assert "Warning (false parameter refinement)" in output
    assert "Parameter 'x'" in output
