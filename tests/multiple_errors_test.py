from aeon.facade.api import AeonError, NonOrderableComparisonError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SynthesisUI

setup_logger()


def _errors(source: str) -> list[AeonError]:
    cfg = AeonConfig(synthesizer="none", synthesis_ui=SynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(cfg)
    return list(driver.parse(aeon_code=source))


def test_single_error_still_reported():
    source = "def main (args : Int) : Int = unknown_name;"
    errors = _errors(source)
    assert len(errors) == 1, errors


def test_multiple_unknown_variables_all_reported():
    """Two distinct top-level definitions each reference an undefined name; the
    elaborator should report both rather than bailing on the first."""
    source = r"""
    def foo (x : Int) : Int = does_not_exist_a;
    def bar (y : Int) : Int = does_not_exist_b;
    def main (args : Int) : Int = 0;
    """
    errors = _errors(source)
    assert len(errors) >= 2, errors


def test_multiple_phase3_errors_all_reported():
    """Errors raised during the unification-removal phase (non-orderable
    comparisons, issue #292) are also collected across definitions."""
    source = r"""
    def foo (x : Int) : Int = if true < false then 0 else 1;
    def bar (y : Int) : Int = if false > true then 0 else 1;
    def main (args : Int) : Int = 0;
    """
    errors = _errors(source)
    assert len(errors) >= 2, errors
    assert all(isinstance(e, NonOrderableComparisonError) for e in errors), errors


def test_valid_program_has_no_errors():
    source = r"""
    def foo (x : Int) : Int = x;
    def main (args : Int) : Int = foo 1;
    """
    assert _errors(source) == []
