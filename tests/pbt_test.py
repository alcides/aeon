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
    # Whatever negative/zero value was first found, shrinking minimizes it to 0
    # (0 > 0 is false and 0 has minimal magnitude).
    assert r.counterexample == ["0"]


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


# --- Algebraic datatype (ADT) generation -----------------------------------

ADT_SOURCE = """
open List

@property(40)
def prop_reverse_preserves_length (l : (List Int)) : Bool =
    length (reversed l) == length l;

@property(60)
def prop_always_empty (l : (List Int)) : Bool =
    length l == 0;
"""


@pytest.fixture(scope="module")
def adt_results():
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SynthesisUI(), synthesis_budget=10, no_main=False)
    driver = AeonDriver(cfg)
    errors = driver.parse(aeon_code=ADT_SOURCE)
    assert errors == [], errors
    rs = run_properties(
        driver.typing_ctx,
        driver.evaluation_ctx,
        driver.core,
        driver.metadata,
        seed=0,
        constructor_names=driver.constructor_names,
    )
    return {r.name.name: r for r in rs}


def test_adt_property_passes(adt_results):
    # Lists are generated as cons/nil trees; a true list property holds.
    r = adt_results["prop_reverse_preserves_length"]
    assert r.passed, r.summary()


def test_adt_generates_non_empty_values(adt_results):
    # A property false for any non-empty list must fail with a cons counterexample,
    # proving the generator produces more than just the empty list.
    r = adt_results["prop_always_empty"]
    assert not r.passed
    assert r.counterexample is not None
    assert "cons" in r.counterexample[0].lower()


def test_adt_counterexample_is_shrunk_to_minimum(adt_results):
    # Constructor-based shrinking reduces any failing list to the minimal one: a
    # single element (tail shrunk to nil) whose value is shrunk to 0.
    r = adt_results["prop_always_empty"]
    assert r.counterexample == ["List_cons 0 List_nil"]
