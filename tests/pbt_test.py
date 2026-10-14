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
def prop_add_commutes (x : Int) (y : Int) : Bool := x + y = y + x;

@property
def prop_all_positive (x : Int) : Bool := x > 0;

@property(150)
def prop_positive_domain (x : {v : Int | v > 0}) : Bool := x > 0;

@property
def prop_below (n : Int) (i : {v : Int | v < n}) : Bool := i < n;

@property
def prop_not_bool (x : Int) : Int := x;
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

def shrink_input : (List Int) := .cons 9 (.cons 3 .nil);

@property(40)
def prop_reverse_preserves_length (l : (List Int)) : Bool :=
    length (reversed l) = length l;

@property(60)
def prop_always_empty (l : (List Int)) : Bool :=
    length l = 0;
"""


@pytest.fixture(scope="module")
def adt_driver():
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SynthesisUI(), synthesis_budget=10, no_main=False)
    driver = AeonDriver(cfg)
    errors = driver.parse(aeon_code=ADT_SOURCE)
    assert errors == [], errors
    return driver


@pytest.fixture(scope="module")
def adt_results(adt_driver):
    driver = adt_driver
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
    # Inputs may use constructors or ordinary list functions.
    r = adt_results["prop_reverse_preserves_length"]
    assert r.passed, r.summary()


def test_adt_generates_non_empty_values(adt_results):
    # A property false for any non-empty list must fail without an evaluation
    # error. The counterexample can now be a function call, not just cons/nil.
    r = adt_results["prop_always_empty"]
    assert not r.passed
    assert r.counterexample is not None
    assert r.error is None


def test_adt_counterexample_is_shrunk_to_minimum(adt_driver):
    # Test structural shrinking on a known constructor expression. Unrestricted
    # generation can instead return a function call, which this shrinker does
    # not promise to normalize into a constructor tree.
    from aeon.core.terms import Application, Var
    from aeon.synthesis.pbt.generators import build_adt_context
    from aeon.synthesis.pbt.runner import (
        _collect_constructors,
        _collect_properties,
        _eval_bool,
        _render,
        _replace_tail,
        _top_level_values,
    )
    from aeon.synthesis.pbt.shrink import minimize

    driver = adt_driver
    spec = next(s for s in _collect_properties(driver.core, driver.metadata)[0] if s.name.name == "prop_always_empty")
    term = next(value for name, value in _top_level_values(driver.core).items() if name.name == "shrink_input")
    constructors = _collect_constructors(driver.core, driver.constructor_names)

    def still_fails(terms):
        call = Application(Var(spec.name), terms[0])
        return _eval_bool(_replace_tail(driver.core, call), driver.evaluation_ctx, 5.0)[0] is False

    minimized = minimize(
        [term],
        [spec.arg_specs[0][1]],
        [True],
        still_fails,
        {b.name.name: b.type for b in constructors},
        driver.constructor_names,
        build_adt_context(driver.typing_ctx, constructors),
    )
    assert [_render(term) for term in minimized] == ["List_cons 0 List_nil"]


@pytest.fixture(scope="module")
def unrestricted_adt_driver():
    driver = AeonDriver(
        AeonConfig(synthesizer="enumerative", synthesis_ui=SynthesisUI(), synthesis_budget=10, no_main=False)
    )
    assert (
        driver.parse(
            aeon_code="""
        inductive Box
        | box (value:Int) : Box

        def make_box (value:Int) : Box := .box value;
        def sample_box : Box := make_box 7;

        @property(40)
        def prop_box (b:Box) : Bool := true;
        """
        )
        == []
    )
    return driver


def test_adt_generation_retains_full_context(unrestricted_adt_driver):
    from aeon.synthesis.pbt.generators import build_adt_context
    from aeon.synthesis.pbt.runner import _iter_top_level
    from aeon.typechecking.context import VariableBinder

    driver = unrestricted_adt_driver
    binders = [VariableBinder(name, ty) for name, ty in _iter_top_level(driver.core)]
    ctx = build_adt_context(driver.typing_ctx, binders)
    assert all(entry in ctx.entries for entry in driver.typing_ctx.entries)
    assert all(binder in ctx.entries for binder in binders)
    assert ctx.trusted_names == driver.typing_ctx.trusted_names
    assert len(driver.typing_ctx.entries) < len(ctx.entries)


def test_adt_generation_uses_ordinary_functions_and_values(unrestricted_adt_driver):
    from aeon.synthesis.pbt.generators import build_adt_context
    from aeon.synthesis.pbt.runner import (
        _collect_properties,
        _generate_property_cases,
        _iter_top_level,
        _term_references,
    )
    from aeon.typechecking.context import VariableBinder

    driver = unrestricted_adt_driver
    binders = [VariableBinder(name, ty) for name, ty in _iter_top_level(driver.core)]
    ctx = build_adt_context(driver.typing_ctx, binders)
    spec = _collect_properties(driver.core, driver.metadata)[0][0]
    cases = _generate_property_cases(spec, driver.typing_ctx, ctx, driver.metadata, seed=0)
    references = {name.name for terms, _ in cases for term in terms for name in _term_references(term)}
    assert "make_box" in references
    assert "sample_box" in references
    results = run_properties(
        driver.typing_ctx,
        driver.evaluation_ctx,
        driver.core,
        driver.metadata,
        seed=0,
        constructor_names=driver.constructor_names,
    )
    assert len(results) == 1
    assert results[0].passed, results[0].summary()
    assert results[0].trials == 40
