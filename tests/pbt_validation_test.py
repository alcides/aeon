"""PBT candidates must pass the same checker as ordinary Aeon programs."""

import pytest

from aeon.core.terms import Application, Literal
from aeon.core.types import t_bool, t_int
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.pbt.generators import TypeSampler, build_adt_context, build_base_context
from aeon.synthesis.pbt.runner import _collect_properties, _iter_top_level, _top_level_values, run_properties
from aeon.synthesis.pbt.shrink import minimize
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import VariableBinder
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name


@pytest.fixture(scope="module")
def validation_program():
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0, no_main=True))
    assert (
        driver.parse(
            aeon_code="""
    open List

    inductive PosList
    | pnil : PosList
    | pcons (hd:{v:Int | v > 10}) (tl:PosList) : PosList

    def valid_pos : PosList := .pcons 11 .pnil;
    def nonempty : (List Int) := .cons 7 .nil;

    def positive (xs:PosList) : Bool :=
        match xs with
        | pnil => true
        | pcons hd tl => hd > 10 && positive tl;

    @property(40)
    def prop_positive (xs:PosList) : Bool := positive xs;

    @property(5)
    def prop_nonempty (xs:{v:(List Int) | List.size v > 0}) : Bool := length xs > 0;
    """
        )
        == []
    )
    binders = [VariableBinder(name, ty) for name, ty in _iter_top_level(driver.core)]
    ctx = build_adt_context(driver.typing_ctx, binders)
    values = {name.name: value for name, value in _top_level_values(driver.core).items()}
    specs = {spec.name.name: spec for spec in _collect_properties(driver.core, driver.metadata)[0]}
    return driver, ctx, values, specs


def invalid_pos(values):
    good = values["valid_pos"]
    assert isinstance(good, Application) and isinstance(good.fun, Application)
    return Application(Application(good.fun.fun, Literal(-1, t_int)), good.arg)


def test_invalid_constructor_field_is_rejected_before_accepting_input(validation_program, monkeypatch):
    from aeon.synthesis.pbt import generators

    driver, ctx, values, specs = validation_program
    spec = specs["prop_positive"]
    ty = spec.arg_specs[0][1]
    bad = invalid_pos(values)
    assert not check_type(ctx, bad, ty)
    proposals = iter([bad, values["valid_pos"]])
    monkeypatch.setattr(generators, "sample_one", lambda *args, **kwargs: next(proposals))
    assert TypeSampler(ctx, ty, spec.name, driver.metadata).sample() == values["valid_pos"]


def test_invalid_adt_domain_reports_generation_failure(validation_program, monkeypatch):
    from aeon.synthesis.pbt import generators

    driver, ctx, values, specs = validation_program
    spec = specs["prop_positive"]
    monkeypatch.setattr(generators, "sample_one", lambda *args, **kwargs: invalid_pos(values))
    with pytest.raises(RuntimeError, match="within 128 attempts"):
        TypeSampler(ctx, spec.arg_specs[0][1], spec.name, driver.metadata).sample()


def test_unrefined_base_inputs_are_also_typechecked(monkeypatch):
    from aeon.synthesis.pbt import generators

    proposals = iter([Literal(True, t_bool), Literal(3, t_int)])
    monkeypatch.setattr(generators, "sample_one", lambda *args, **kwargs: next(proposals))
    assert TypeSampler(build_base_context(), t_int, Name("property"), {}).sample() == Literal(3, t_int)


def test_measure_refined_target_is_checked(validation_program, monkeypatch):
    from aeon.synthesis.pbt import generators

    driver, ctx, values, specs = validation_program
    good = values["nonempty"]
    empty = good.arg
    spec = specs["prop_nonempty"]
    ty = spec.arg_specs[0][1]
    assert not check_type(ctx, empty, ty)
    assert check_type(ctx, good, ty)
    proposals = iter([empty, good])
    monkeypatch.setattr(generators, "sample_one", lambda *args, **kwargs: next(proposals))
    assert TypeSampler(ctx, ty, spec.name, driver.metadata).sample() == good


def test_checker_errors_fail_closed(monkeypatch):
    from aeon.synthesis.pbt import generators

    monkeypatch.setattr(generators, "sample_one", lambda *args, **kwargs: Literal(3, t_int))

    def unsupported(*args):
        raise NotImplementedError("unsupported domain")

    monkeypatch.setattr(generators, "check_type", unsupported)
    with pytest.raises(RuntimeError, match="validation raised NotImplementedError: unsupported domain"):
        TypeSampler(build_base_context(), t_int, Name("property"), {}).sample()


def test_shrinking_never_evaluates_an_invalid_adt(validation_program, monkeypatch):
    from aeon.synthesis.pbt import shrink

    driver, ctx, values, specs = validation_program
    good = values["valid_pos"]
    bad = invalid_pos(values)
    monkeypatch.setattr(shrink, "shrinks", lambda *args: iter([bad]))
    evaluated = []

    def still_fails(terms):
        evaluated.append(terms)
        return True

    result = minimize([good], [specs["prop_positive"].arg_specs[0][1]], [True], still_fails, {}, set(), ctx)
    assert result == [good]
    assert evaluated == []


def test_shrinking_preserves_measure_refinement(validation_program):
    driver, ctx, values, specs = validation_program
    constructors = {name.name: ty for name, ty in _iter_top_level(driver.core) if name.name in driver.constructor_names}
    good = values["nonempty"]
    ty = specs["prop_nonempty"].arg_specs[0][1]
    evaluated = []

    def still_fails(terms):
        assert check_type(ctx, terms[0], ty)
        evaluated.append(terms[0])
        return True

    result = minimize([good], [ty], [True], still_fails, constructors, driver.constructor_names, ctx)
    assert evaluated
    assert check_type(ctx, result[0], ty)
    assert result[0] != good.arg


def test_positive_adt_property_does_not_get_out_of_domain_counterexamples(validation_program):
    driver, _, _, _ = validation_program
    results = run_properties(
        driver.typing_ctx,
        driver.evaluation_ctx,
        driver.core,
        driver.metadata,
        seed=0,
        constructor_names=driver.constructor_names,
    )
    positive = next(result for result in results if result.name.name == "prop_positive")
    assert positive.passed, positive.summary()
    assert positive.trials == 40


@pytest.fixture(scope="module")
def partial_input_program():
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0, no_main=True))
    assert (
        driver.parse(
            aeon_code="""
        open List
        import Math;
        def bad (_:Unit) : (List Int) := .cons (Math.floor Math.INF) .nil;
        def good : (List Int) := .cons 7 .nil;
        @property(2)
        def prop_length (xs:(List Int)) : Bool := length xs >= 0;
        @property(2)
        def prop_crashes (xs:(List Int)) : Bool := Math.floor Math.INF = 0;
    """
        )
        == []
    )
    from aeon.core.terms import Var

    bindings = {name.name: name for name, _ in _iter_top_level(driver.core)}
    bad = Application(Var(bindings["bad"]), Var(Name("unit", 0)))
    good = Var(bindings["good"])
    return driver, bad, good


def test_partial_input_is_resampled_but_property_exceptions_still_fail(partial_input_program, monkeypatch):
    from aeon.synthesis.pbt import generators

    driver, bad, good = partial_input_program
    proposals = iter([bad, good, good, bad, good])
    monkeypatch.setattr(generators, "sample_one", lambda *args, **kwargs: next(proposals))
    results = run_properties(driver.typing_ctx, driver.evaluation_ctx, driver.core, driver.metadata)
    by_name = {result.name.name: result for result in results}
    assert by_name["prop_length"].passed
    assert by_name["prop_length"].trials == 2
    assert not by_name["prop_crashes"].passed
    assert "OverflowError" in by_name["prop_crashes"].error


def test_only_partial_inputs_report_generation_failure(partial_input_program, monkeypatch):
    from aeon.synthesis.pbt import generators

    driver, bad, _ = partial_input_program
    monkeypatch.setattr(generators, "sample_one", lambda *args, **kwargs: bad)
    results = run_properties(driver.typing_ctx, driver.evaluation_ctx, driver.core, driver.metadata)
    assert all(not result.passed and result.trials == 0 for result in results)
    assert all("input generation failed" in result.error for result in results)
    assert all(result.counterexample is None for result in results)


def test_shared_inputs_respect_each_property_exclusion(partial_input_program, monkeypatch):
    from dataclasses import replace
    from aeon.core.terms import If, Var
    from aeon.synthesis.pbt.runner import _generate_property_cases

    driver, _, good = partial_input_program
    specs = _collect_properties(driver.core, driver.metadata)[0]
    first, second = [replace(spec, samples=1) for spec in specs]
    binders = [VariableBinder(name, ty) for name, ty in _iter_top_level(driver.core)]
    ctx = build_adt_context(driver.typing_ctx, binders)
    calls_second = If(Application(Var(second.name), good), good, good)
    assert check_type(ctx, calls_second, first.arg_specs[0][1])
    proposals = iter([calls_second, good])
    monkeypatch.setattr(TypeSampler, "sample", lambda *args, **kwargs: next(proposals))
    cache = {}
    first_cases = _generate_property_cases(first, driver.typing_ctx, ctx, driver.metadata, 0, case_cache=cache)
    second_cases = _generate_property_cases(second, driver.typing_ctx, ctx, driver.metadata, 0, case_cache=cache)
    assert first_cases[0][0] == [calls_second]
    assert second_cases[0][0] == [good]
