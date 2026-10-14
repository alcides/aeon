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
