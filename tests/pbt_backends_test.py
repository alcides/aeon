"""Input search backends share validation and preserve their search state."""

import pytest

from aeon.core.terms import Hole, Literal
from aeon.core.types import AbstractionType, t_bool, t_int
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.identification import get_holes
from aeon.synthesis.pbt.generators import TypeSampler, build_adt_context, build_base_context
from aeon.synthesis.pbt.runner import _iter_top_level, _render, run_properties
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import VariableBinder
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name

BACKENDS = ("enumerative", "random_search", "tdsyn", "tdsyn_enumerative", "tdsyn_random")


@pytest.fixture(scope="module")
def refined_program():
    from aeon.synthesis.pbt.runner import _collect_properties

    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0, no_main=True))
    assert driver.parse(aeon_code="@property(8)\ndef prop (x:{v:Int | v > 10}) : Bool := x > 10;") == []
    return driver, _collect_properties(driver.core, driver.metadata)[0][0]


@pytest.mark.parametrize("backend", BACKENDS)
def test_backend_produces_multiple_checked_inputs(backend):
    ctx = build_base_context()
    sampler = TypeSampler(ctx, t_int, Name("property"), {}, synthesizers=backend, seed=17)
    samples = [sampler.sample() for _ in range(8)]
    assert all(check_type(ctx, term, t_int) for term in samples)
    assert len({_render(term) for term in samples}) >= 3
    assert sampler.backend_counts == {backend: 8}


@pytest.mark.parametrize("backend", BACKENDS)
def test_backend_respects_refined_inputs(backend, refined_program):
    driver, spec = refined_program
    ty = spec.arg_specs[0][1]
    sampler = TypeSampler(
        build_base_context(),
        ty,
        spec.name,
        driver.metadata,
        validation_ctx=driver.typing_ctx,
        synthesizers=backend,
    )
    assert all(check_type(driver.typing_ctx, sampler.sample(), ty) for _ in range(8))


@pytest.mark.parametrize("backend", BACKENDS)
def test_backend_is_reproducible(backend):
    def corpus():
        sampler = TypeSampler(build_base_context(), t_int, Name("property"), {}, seed=9, synthesizers=backend)
        return [_render(sampler.sample()) for _ in range(12)]

    assert corpus() == corpus()


def test_multiple_backends_rotate_without_restarting_enumeration():
    names = ("enumerative", "random_search", "tdsyn_enumerative", "tdsyn_random")
    sampler = TypeSampler(build_base_context(), t_int, Name("property"), {}, synthesizers=names)
    samples = [sampler.sample() for _ in range(32)]
    assert sampler.backend_counts == dict.fromkeys(names, 8)
    assert len({_render(term) for term in samples[::4]}) == 8


@pytest.mark.parametrize("backend", BACKENDS)
def test_all_backends_reject_invalid_and_partial_proposals(monkeypatch, backend):
    from aeon.synthesis.pbt import generators

    proposals = iter([Literal(False, t_bool), Hole(Name("unfinished")), Literal(12, t_int)])
    monkeypatch.setattr(generators, "input_candidates", lambda *args: proposals)
    monkeypatch.setattr(generators, "sample_one", lambda *args, **kwargs: next(proposals))
    assert TypeSampler(build_base_context(), t_int, Name("property"), {}, synthesizers=backend).sample() == Literal(
        12, t_int
    )


@pytest.fixture(scope="module")
def box_program():
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0, no_main=True))
    assert (
        driver.parse(
            aeon_code="""
    inductive Box
    | box (value:{v:Int | v > 10}) : Box
    def make_box (value:{v:Int | v > 10}) : Box := .box value;
    @property(8)
    def prop_box (b:Box) : Bool := true;
    """
        )
        == []
    )
    binders = [VariableBinder(name, ty) for name, ty in _iter_top_level(driver.core)]
    return driver, build_adt_context(driver.typing_ctx, binders)


@pytest.mark.parametrize("backend", BACKENDS)
def test_backend_generates_refined_adt_inputs(box_program, backend):
    driver, ctx = box_program
    from aeon.synthesis.pbt.runner import _collect_properties

    spec = _collect_properties(driver.core, driver.metadata)[0][0]
    sampler = TypeSampler(ctx, spec.arg_specs[0][1], spec.name, driver.metadata, synthesizers=backend)
    assert all(check_type(ctx, sampler.sample(), spec.arg_specs[0][1]) for _ in range(8))


def test_mixed_backends_also_rotate_for_dependent_arguments(monkeypatch):
    calls = []
    original = TypeSampler.sample

    def observe(self, synthesizer=None):
        calls.append(synthesizer)
        return original(self, synthesizer)

    monkeypatch.setattr(TypeSampler, "sample", observe)
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0, no_main=True))
    assert (
        driver.parse(
            aeon_code="""
    @property(8)
    def prop_below (n:Int) (i:{v:Int | v < n}) : Bool := i < n;
    """
        )
        == []
    )
    names = ("enumerative", "random_search", "tdsyn_enumerative", "tdsyn_random")
    results = run_properties(
        driver.typing_ctx,
        driver.evaluation_ctx,
        driver.core,
        driver.metadata,
        input_synthesizers=names,
    )
    assert results[0].passed, results[0].summary()
    assert calls == [name for _ in range(2) for name in names for _arg in range(2)]


@pytest.mark.parametrize("backend", ("backward_lit", "tdsyn_backward"))
def test_directional_variants_produce_complete_inputs(backend):
    sampler = TypeSampler(build_base_context(), t_int, Name("property"), {}, synthesizers=backend)
    assert all(not get_holes(sampler.sample()) for _ in range(5))


def test_abstraction_variant_finishes_its_subgoals():
    ctx = build_base_context()
    ty = AbstractionType(Name("x"), t_int, t_int)
    term = TypeSampler(ctx, ty, Name("property"), {}, synthesizers="backward_abs").sample()
    assert not get_holes(term)
    assert check_type(ctx, term, ty)


@pytest.mark.parametrize(
    "backend",
    (
        "backward_close",
        "backward_app",
        "backward_if",
        "forward_close",
        "forward_let_app",
        "forward_let_if",
        "forward_let_tapp",
        "forward_let_abs",
        "forward_let_tabs",
    ),
)
def test_other_directional_variants_finish_their_subgoals(backend):
    from aeon.core.types import Kind, TypePolymorphism, TypeVar

    x, a = Name("x", 0), Name("a", 1)
    ctx = build_base_context().with_var(Name("value", 0), t_int)
    ctx = ctx.with_var(Name("identity", 0), AbstractionType(x, t_int, t_int))
    ctx = ctx.with_var(Name("poly", 0), TypePolymorphism(a, Kind.BASE, AbstractionType(x, TypeVar(a), TypeVar(a))))
    term = TypeSampler(ctx, t_int, Name("property"), {}, synthesizers=backend).sample()
    assert not get_holes(term)
    assert check_type(ctx, term, t_int)


def test_cli_accepts_multiple_independent_input_backends(monkeypatch):
    from aeon.__main__ import parse_arguments

    monkeypatch.setattr(
        "sys.argv",
        [
            "aeon",
            "--test",
            "-s",
            "tdsyn",
            "--input-synthesizer",
            "enumerative",
            "--input-synthesizer",
            "tdsyn_random",
            "examples/testing/list_laws.ae",
        ],
    )
    args = parse_arguments()
    assert args.synthesizer == "tdsyn"
    assert args.input_synthesizer == ["enumerative", "tdsyn_random"]


def test_fixed_property_corpora_can_mix_backends():
    from aeon.synthesis.identification import incomplete_functions_and_holes
    from aeon.synthesis.pbt.runner import property_corpora_for_target
    from tests.driver import check_and_return_core

    core, ctx, _, metadata = check_and_return_core("""
    def f (x:Int) : Bool := ?hole;
    @property(8)
    def prop_f (x:Int) : Bool := f x;
    """)
    target = incomplete_functions_and_holes(ctx, core)[0][0]

    def corpus():
        return property_corpora_for_target(
            ctx,
            core,
            metadata,
            target,
            {target},
            seed=7,
            input_synthesizers=("enumerative", "tdsyn_random"),
        )[0]

    cases = corpus().cases
    assert cases == corpus().cases
    assert len(cases) == 8
    assert len({_render(case[0]) for case in cases[::2]}) == 4


def test_inapplicable_variant_reports_generation_failure():
    with pytest.raises(RuntimeError, match="backward_abs exhausted"):
        TypeSampler(build_base_context(), t_int, Name("property"), {}, synthesizers="backward_abs").sample()


@pytest.mark.parametrize("names", ((), ("not_a_backend",)))
def test_invalid_backend_configuration_is_rejected(names):
    with pytest.raises(ValueError, match="Unsupported PBT"):
        TypeSampler(build_base_context(), t_int, Name("property"), {}, synthesizers=names)
