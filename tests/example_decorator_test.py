"""Tests for the @example decorator.

A single ``@example(assertion)`` plays three roles, exercised here:

  * documentation  - surfaced by the HTML doc generator,
  * test case       - checked by the ``--test`` runner (``run_examples``),
  * synthesis goal  - recorded as a fitness objective in the metadata.
"""

from __future__ import annotations

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.pbt import run_examples
from aeon.synthesis.uis.api import SynthesisUI


def _driver(source: str) -> AeonDriver:
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SynthesisUI(), synthesis_budget=10, no_main=False)
    driver = AeonDriver(cfg)
    errors = driver.parse(aeon_code=source)
    assert errors == [], errors
    return driver


PASSING = """
@example(my_abs (0 - 3) = 3)
@example(my_abs 5 = 5)
def my_abs (x : Int) : Int := if x < 0 then 0 - x else x;

def main (_ : Int) : Unit := print 0;
"""


def test_passing_examples_all_pass():
    driver = _driver(PASSING)
    results = run_examples(driver.evaluation_ctx, driver.core, driver.metadata)
    assert len(results) == 2
    assert all(r.passed for r in results), [r.summary() for r in results]


def test_failing_example_is_reported():
    source = """
        @example(wrong 1 = 1)
        @example(wrong 1 = 2)
        def wrong (x : Int) : Int := x;

        def main (_ : Int) : Unit := print 0;
    """
    driver = _driver(source)
    results = run_examples(driver.evaluation_ctx, driver.core, driver.metadata)
    by_passed = {r.passed for r in results}
    assert by_passed == {True, False}
    failing = [r for r in results if not r.passed]
    assert len(failing) == 1
    assert "False" in (failing[0].error or "")


def test_driver_has_tests_and_run_tests_counts_examples():
    driver = _driver(PASSING)
    assert driver.has_tests()
    failures = driver.run_tests()
    assert failures == []


def test_example_records_synthesis_goal():
    # Each @example contributes a minimize goal so a fitness-based synthesizer is
    # driven to satisfy it (programming-by-example).
    driver = _driver(PASSING)
    goal_entries = [v for v in driver.metadata.values() if isinstance(v, dict) and "goals" in v]
    assert goal_entries, "expected an @example to register a synthesis goal"
    goals = goal_entries[0]["goals"]
    assert len(goals) == 2
    assert all(g.minimize for g in goals)


def test_example_assertion_must_be_bool():
    # A non-Bool assertion is a type error (the synthesis goal wraps it in an if).
    source = """
        @example(bad 1)
        def bad (x : Int) : Int := x;

        def main (_ : Int) : Unit := print 0;
    """
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SynthesisUI(), synthesis_budget=10, no_main=False)
    driver = AeonDriver(cfg)
    errors = driver.parse(aeon_code=source)
    assert errors != []


def test_examples_surface_in_documentation():
    from aeon.documentation.generator import extract_documentation, generate_html

    doc = extract_documentation("inline.ae", source=PASSING)
    fn = next(f for f in doc.functions if f.name == "my_abs")
    assert fn.examples == ["my_abs (0 - 3) = 3", "my_abs 5 = 5"]
    # The @example decorator is rendered as an examples block, not a chip.
    assert all("example" not in d for d in fn.decorators)

    html = generate_html(doc)
    assert "my_abs (0 - 3) = 3" in html
    assert "Examples" in html


def test_numeric_example_records_training_data():
    # A numeric `f(lits) == lit` example also feeds the decision-tree synthesizer
    # as a training point [args..., expected].
    source = """
        @example(f 1.0 = 2.0)
        @example(f 2.0 = 4.0)
        def f (x : Float) : Float := x + x;

        def main (_ : Int) : Unit := print 0;
    """
    driver = _driver(source)
    data = [v["training_data"] for v in driver.metadata.values() if isinstance(v, dict) and "training_data" in v]
    assert data == [[[1.0, 2.0], [2.0, 4.0]]]


def test_non_numeric_examples_do_not_record_training_data():
    # Bool examples (and non-equality assertions) carry no numeric expected value,
    # so they must not produce decision-tree training points.
    source = """
        @example(p 35 64)
        @example(p 1 1 = false)
        def p (a : Int) (b : Int) : Bool := a = b;

        def main (_ : Int) : Unit := print 0;
    """
    driver = _driver(source)
    assert not any(isinstance(v, dict) and "training_data" in v for v in driver.metadata.values())


@pytest.mark.skip(reason="Synthesis-only")
def test_example_drives_decision_tree_synthesis():
    # The decision-tree synthesizer learns a function purely from @example points.
    from aeon.synthesis.entrypoint import synthesize_holes
    from aeon.synthesis.identification import incomplete_functions_and_holes
    from aeon.synthesis.modules.decision_tree import DecisionTreeSynthesizer

    from tests.driver import check_and_return_core

    source = """
        @example(f 1.0 = 10.0)
        @example(f 2.0 = 10.0)
        @example(f 8.0 = 20.0)
        @example(f 9.0 = 20.0)
        def f (x : Float) : Float := ?hole;
    """
    core, ctx, ectx, md = check_and_return_core(source)
    incs = incomplete_functions_and_holes(ctx, core)
    mapping = synthesize_holes(ctx, ectx, core, incs, md, synthesizer=DecisionTreeSynthesizer(), budget=5)
    assert any(v is not None for v in mapping.values())


@pytest.mark.skip(reason="Synthesis-only")
def test_example_drives_synthesis():
    # With a hole body and a fitness-based synthesizer, the @example goals should
    # steer the search toward a body that satisfies them.
    source = """
        @example(double 3 = 6)
        @example(double 0 = 0)
        @example(double 5 = 10)
        def double (x : Int) : Int := ?hole;

        def main (_ : Int) : Unit := print 0;
    """
    cfg = AeonConfig(synthesizer="gp", synthesis_ui=SynthesisUI(), synthesis_budget=10, no_main=False)
    driver = AeonDriver(cfg)
    errors = driver.parse(aeon_code=source)
    assert errors == [], errors
    assert driver.has_synth()
    term = driver.synth()
    assert term is not None
