from aeon.facade.api import NonOrderableComparisonError
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


def test_int_comparison_ok():
    assert _run("def main (args : Int) : Int = if 1 < 2 then 0 else 1;") == 0


def test_float_comparison_ok():
    assert _run("def main (args : Int) : Int = if 1.0 >= 2.0 then 0 else 1;") == 1


def test_string_comparison_ok():
    assert _run('def main (args : Int) : Int = if "a" < "b" then 0 else 1;') == 0


def test_polymorphic_helper_at_int_ok():
    source = r"""
    def cmp (x : Int) (y : Int) : Bool = x < y;
    def main (args : Int) : Int = if cmp 2 1 then 0 else 1;
    """
    assert _run(source) == 1


def test_bool_comparison_rejected():
    errors = _errors("def main (args : Int) : Int = if true < false then 0 else 1;")
    assert any(isinstance(e, NonOrderableComparisonError) for e in errors), errors


def test_set_comparison_rejected():
    source = r"""
    def main (args : Int) : Int =
        let s : Set = Set_empty in
        if s < s then 0 else 1;
    """
    errors = _errors(source)
    assert any(isinstance(e, NonOrderableComparisonError) for e in errors), errors


def test_gt_bool_comparison_rejected():
    errors = _errors("def main (args : Int) : Int = if true > false then 0 else 1;")
    assert any(isinstance(e, NonOrderableComparisonError) for e in errors), errors
