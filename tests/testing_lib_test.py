"""Tests for the Testing library (libraries/Testing.ae) and its integration
with the ``--test`` property/unit-test runner.

A *unit test* in Aeon is a zero-argument ``@property`` returning ``Bool``; a
*property test* is a ``@property`` with arguments whose inputs are generated.
The Testing library only adds readable ``Bool``-valued assertion combinators on
top, so we drive everything through the same ``run_properties`` runner used by
the rest of the PBT framework and assert on the results.
"""

from pathlib import Path

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.pbt import run_properties
from aeon.synthesis.uis.api import SynthesisUI

REPO_ROOT = Path(__file__).resolve().parent.parent
TESTING_EXAMPLES_DIR = REPO_ROOT / "examples" / "testing"
EXAMPLE_SUITES = sorted(TESTING_EXAMPLES_DIR.glob("*.ae"))

# A self-contained program exercising every assertion combinator: passing and
# failing instances of each, so we can assert the runner classifies both.
SOURCE = """
open Testing

@property(1)
def t_assertTrue_pass : Bool = assertTrue (1 < 2);
@property(1)
def t_assertTrue_fail : Bool = assertTrue (2 < 1);

@property(1)
def t_assertFalse_pass : Bool = assertFalse (2 < 1);

@property(1)
def t_assertEqual_pass : Bool = assertEqual (3 * 4) 12;
@property(1)
def t_assertEqual_fail : Bool = assertEqual (3 * 4) 13;

@property(1)
def t_assertNotEqual_pass : Bool = assertNotEqual 1 2;

@property(1)
def t_assertLess_pass : Bool = assertLess 1 2;
@property(1)
def t_assertGreaterEqual_pass : Bool = assertGreaterEqual 2 2;

@property(1)
def t_assertClose_pass : Bool = assertClose (0.1 + 0.2) 0.3 0.0001;
@property(1)
def t_assertClose_fail : Bool = assertClose 1.0 2.0 0.1;

@property(1)
def t_both_pass : Bool = both (assertEqual 1 1) (assertLess 1 2);
@property(1)
def t_allOf3_pass : Bool = allOf3 (assertTrue true) (assertEqual 2 2) (assertFalse false);
@property(1)
def t_allOf3_fail : Bool = allOf3 (assertTrue true) (assertEqual 2 3) (assertFalse false);

# A genuine property (generated input) phrased with the assertion vocabulary.
@property
def prop_abs_nonneg (x : Int) : Bool = assertGreaterEqual (x * x) 0;
"""


@pytest.fixture(scope="module")
def results():
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SynthesisUI(), synthesis_budget=10, no_main=False)
    driver = AeonDriver(cfg)
    errors = driver.parse(aeon_code=SOURCE)
    assert errors == [], errors
    rs = run_properties(driver.typing_ctx, driver.evaluation_ctx, driver.core, driver.metadata, seed=0)
    return {r.name.name: r for r in rs}


@pytest.mark.parametrize(
    "name",
    [
        "t_assertTrue_pass",
        "t_assertFalse_pass",
        "t_assertEqual_pass",
        "t_assertNotEqual_pass",
        "t_assertLess_pass",
        "t_assertGreaterEqual_pass",
        "t_assertClose_pass",
        "t_both_pass",
        "t_allOf3_pass",
        "prop_abs_nonneg",
    ],
)
def test_assertions_that_should_pass(results, name):
    assert results[name].passed, results[name].summary()


@pytest.mark.parametrize(
    "name",
    [
        "t_assertTrue_fail",
        "t_assertEqual_fail",
        "t_assertClose_fail",
        "t_allOf3_fail",
    ],
)
def test_assertions_that_should_fail(results, name):
    assert not results[name].passed, results[name].summary()


@pytest.mark.parametrize("suite", EXAMPLE_SUITES, ids=lambda p: p.stem)
def test_example_suites_all_pass(suite):
    """Every shipped suite under examples/testing/ must pass end-to-end. This
    also guards the libraries those suites exercise (e.g. the Image_diff_mse
    native float cast and the Set.ae rewrite)."""
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SynthesisUI(), synthesis_budget=10, no_main=False)
    driver = AeonDriver(cfg)
    errors = driver.parse(str(suite))
    assert errors == [], errors
    failures = driver.run_tests(seed=0)
    assert failures == [], [f.summary() for f in failures]


def test_example_suites_discovered():
    """Guard against the glob silently finding nothing (which would make the
    parametrized test vacuously pass)."""
    assert len(EXAMPLE_SUITES) >= 9
