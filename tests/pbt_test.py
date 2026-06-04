"""Tests for the property-based testing framework (issue #37).

All properties live in a single source so the (SMT-heavy) parse/typecheck runs
once; the runner then checks every property and we assert on the results.
"""

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.pbt import run_properties
from aeon.synthesis.uis.api import SynthesisUI

SOURCE = """
@property
def prop_add_commutes (x : Int) (y : Int) : Bool = x + y == y + x;

@property
def prop_all_positive (x : Int) : Bool = x > 0;

@property(150)
def prop_positive_domain (x : {v : Int | v > 0}) : Bool = x > 0;

@property
def prop_below (n : Int) (i : {v : Int | v < n}) : Bool = i < n;

@property
def prop_not_bool (x : Int) : Int = x;
"""


@pytest.fixture(scope="module")
def results():
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SynthesisUI(), synthesis_budget=10, no_main=False)
    driver = AeonDriver(cfg)
    errors = driver.parse(aeon_code=SOURCE)
    assert errors == [], errors
    rs = run_properties(driver.typing_ctx, driver.evaluation_ctx, driver.core, driver.metadata, seed=0)
    return {r.name.name: r for r in rs}


def test_passing_property_reports_success(results):
    r = results["prop_add_commutes"]
    assert r.passed
    assert r.counterexample is None
    assert r.trials > 0


def test_false_property_yields_counterexample(results):
    r = results["prop_all_positive"]
    assert not r.passed
    assert r.counterexample is not None and len(r.counterexample) == 1


def test_refined_domain_only_generates_valid_inputs(results):
    # If a non-positive input were ever generated, this property — which merely
    # restates its own precondition — would fail. It must always pass.
    r = results["prop_positive_domain"]
    assert r.passed, r.summary()
    assert r.trials == 150


def test_dependent_arguments_respect_earlier_choices(results):
    # i is drawn from {v | v < n} after n is chosen; a failure would mean the
    # dependency between arguments was not honoured during generation.
    r = results["prop_below"]
    assert r.passed, r.summary()


def test_non_bool_property_is_skipped(results):
    r = results["prop_not_bool"]
    assert r.passed  # skipped, not failed
    assert r.error is not None and "Bool" in r.error
