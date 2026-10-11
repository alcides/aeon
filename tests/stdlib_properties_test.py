"""Standard-library laws exercise Aeon's synthesis-backed input generation."""

from pathlib import Path

import pytest
from z3 import Solver, String, StringVal, sat

from aeon.core.terms import Literal
from aeon.core.types import t_string
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.pbt import run_properties
from aeon.synthesis.pbt.generators import TypeSampler, build_base_context
from aeon.synthesis.modules.tdsyn.smt_solve import _extract_solution
from aeon.synthesis.modules.tdsyn.worklist import fresh_hole
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.name import Name

ROOT = Path(__file__).resolve().parents[1]
SUITES = ("math_properties", "string_properties", "list_laws", "map_laws", "set_laws", "stack_properties")
COUNTS = (3, 4, 4, 2, 2, 1)


def driver_for(source, filename=None):
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0, no_main=True))
    errors = driver.parse(filename=filename, aeon_code=source)
    assert not errors, errors
    return driver


@pytest.mark.parametrize("suite,count", list(zip(SUITES, COUNTS)))
def test_stdlib_laws_complete_without_skips(suite, count):
    path = ROOT / "examples" / "testing" / f"{suite}.ae"
    driver = driver_for(path.read_text(), str(path))
    for seed in (0, 17):
        results = run_properties(
            driver.typing_ctx,
            driver.evaluation_ctx,
            driver.core,
            driver.metadata,
            seed=seed,
            constructor_names=driver.constructor_names,
        )
        assert len(results) == count
        assert all(r.passed and r.error is None and r.trials >= 25 for r in results), [r.summary() for r in results]


def test_dependent_strings_are_generated_through_shared_synthesis(monkeypatch):
    from aeon.synthesis.pbt import generators
    from aeon.core.types import t_int

    observed = []
    walk = generators.sample_one

    def observe(*args, **kwargs):
        term = walk(*args, **kwargs)
        if isinstance(term, Literal):
            observed.append(term)
        return term

    monkeypatch.setattr(generators, "sample_one", observe)
    source = """
import String
@property(20)
def prop_slice (s:{v:String | 4 <= String.len v && String.len v <= 12})
    (i:{v:Int | 0 <= v && v < String.len s})
    (j:{v:Int | i <= v && v <= String.len s}) : Bool :=
    String.len (String.slice s i j) = j - i;
"""
    driver = driver_for(source)
    results = run_properties(driver.typing_ctx, driver.evaluation_ctx, driver.core, driver.metadata, seed=0)
    assert len(results) == 1 and results[0].passed and results[0].error is None
    strings = [t.value for t in observed if t.type == t_string]
    assert len(strings) == 20
    assert all(4 <= len(s) <= 12 for s in strings)
    assert any(s not in {"", "a", "b", "hello", " "} for s in strings)
    assert len(set(strings)) > 1
    assert any(t.type == t_int for t in observed)


def test_mutated_slice_law_fails_with_an_in_domain_counterexample():
    source = """
import String
@property(20)
def prop_off_by_one (s:{v:String | 4 <= String.len v && String.len v <= 12})
    (i:{v:Int | 0 <= v && v < String.len s})
    (j:{v:Int | i <= v && v <= String.len s}) : Bool :=
    String.len (String.slice s i j) = j - i + 1;
"""
    driver = driver_for(source)
    results = run_properties(driver.typing_ctx, driver.evaluation_ctx, driver.core, driver.metadata, seed=0)
    result = results[0]
    assert not result.passed and result.error is None and result.counterexample
    from aeon.sugar.parser import parse_expression

    s = parse_expression(result.counterexample[0]).value
    i, j = map(int, result.counterexample[1:])
    assert 4 <= len(s) <= 12 and 0 <= i < len(s) and i <= j <= len(s)
    assert len(s[i:j]) != j - i + 1


@pytest.mark.parametrize("value", ["", 'quote"', "Ω", "🙂", "a\n\t"])
def test_smt_string_models_decode_as_python_characters(value):
    var = String("generated")
    solver = Solver()
    solver.add(var == StringVal(value))
    assert solver.check() == sat
    _, hole = fresh_hole(t_string, build_base_context(), path=())
    result = _extract_solution(solver.model(), [hole], {str(hole.name): var})
    assert result[hole.name].value == value


def test_smt_failure_cannot_fall_back_to_an_invalid_base_literal(monkeypatch):
    from aeon.core.types import RefinedType, t_int
    from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
    from aeon.synthesis.pbt import generators

    name = Name("v")
    ty = RefinedType(name, t_int, LiquidApp(Name(">"), [LiquidVar(name), LiquidLiteralInt(10)]))
    monkeypatch.setattr(generators, "sample_one", lambda *args, **kwargs: Literal(0, t_int))
    with pytest.raises(RuntimeError, match="failed to produce"):
        TypeSampler(build_base_context(), ty, Name("property"), {}).sample()


def test_empty_input_domain_is_reported_without_claiming_a_pass():
    driver = driver_for("""
@property(5)
def prop_impossible (x:{v:Int | v > 0 && v < 0}) : Bool := true;
@property(5)
def prop_still_runs (x:Int) : Bool := x = x;
""")
    results = run_properties(driver.typing_ctx, driver.evaluation_ctx, driver.core, driver.metadata)
    assert len(results) == 2
    assert not results[0].passed and results[0].trials == 0
    assert "input generation failed" in results[0].error
    assert results[1].passed and results[1].trials == 5
