from __future__ import annotations

from typing import Any, Callable

from aeon.core.substitutions import substitution
from aeon.core.terms import Literal, Term
from aeon.core.types import Type, t_bool
from aeon.decorators import Metadata
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.api import Synthesizer
from aeon.synthesis.entrypoint import make_program, synthesize_holes
from aeon.synthesis.grammar.ge_synthesis import GESynthesizer
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.pbt.runner import make_property_fitness, property_corpora_for_target, run_properties
from aeon.synthesis.uis.api import SilentSynthesisUI, SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name

from tests.driver import check_and_return_core


class _PropertySelectingSynthesizer(Synthesizer):
    """Try false before true and let the provided fitness choose between them."""

    seen_goals: list[Any]
    seen_scores: list[list[float]]

    def synthesize(
        self,
        ctx: TypingContext,
        type: Type,
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        fun_name: Name,
        metadata: Metadata,
        budget: float = 60,
        ui: SynthesisUI = SynthesisUI(),
        output_value: Callable[[Term], object] | None = None,
    ) -> Term:
        candidates = [Literal(False, t_bool), Literal(True, t_bool)]
        assert all(validate(candidate) for candidate in candidates)
        self.seen_goals = metadata[fun_name]["goals"]
        self.seen_scores = [evaluate(candidate) for candidate in candidates]
        return min(zip(self.seen_scores, candidates), key=lambda pair: pair[0])[1]


def _corpora(source: str):
    core, ctx, ectx, metadata = check_and_return_core(source)
    targets = incomplete_functions_and_holes(ctx, core)
    fun_name, holes = targets[0]
    corpora = property_corpora_for_target(ctx, core, metadata, fun_name, {name for name, _ in targets})
    return core, ctx, ectx, metadata, fun_name, holes[0], corpora


def test_property_corpus_scores_failed_cases_and_is_deterministic():
    source = """
    def f (x : Int) : Bool := ?hole;
    @property(12)
    def prop_f (x : Int) : Bool := f x;
    """
    core, ctx, ectx, metadata, fun_name, hole_name, corpora = _corpora(source)
    again = property_corpora_for_target(ctx, core, metadata, fun_name, {fun_name})

    assert len(corpora) == 1
    assert len(corpora[0].cases) == 12
    assert corpora[0].cases == again[0].cases

    fitness = make_property_fitness(corpora[0], ectx)
    replace = make_program(core, hole_name)
    assert fitness(replace(Literal(True, t_bool))) == 0.0
    assert fitness(replace(Literal(False, t_bool))) == 12.0


def test_property_corpus_respects_refined_dependent_arguments():
    source = """
    def f (n : Int) (i : {v : Int | v < n}) : Bool := ?hole;
    @property(25)
    def prop_f (n : Int) (i : {v : Int | v < n}) : Bool := f n i;
    """
    *_, corpora = _corpora(source)

    assert len(corpora[0].cases) == 25
    assert all(isinstance(n, Literal) and isinstance(i, Literal) and i.value < n.value for n, i in corpora[0].cases)


def test_only_relevant_single_target_properties_are_selected():
    source = """
    def f (x : Int) : Bool := ?hf;
    def g (x : Int) : Bool := ?hg;
    @property(3)
    def prop_f (x : Int) : Bool := f x;
    @property(3)
    def prop_g (x : Int) : Bool := g x;
    @property(3)
    def prop_relational (x : Int) : Bool := f x = g x;
    """
    core, ctx, _, metadata = check_and_return_core(source)
    targets = incomplete_functions_and_holes(ctx, core)
    names = {name.name: name for name, _ in targets}
    open_targets = set(names.values())

    f_corpora = property_corpora_for_target(ctx, core, metadata, names["f"], open_targets)
    g_corpora = property_corpora_for_target(ctx, core, metadata, names["g"], open_targets)

    assert [corpus.spec.name.name for corpus in f_corpora] == ["prop_f"]
    assert [corpus.spec.name.name for corpus in g_corpora] == ["prop_g"]


def test_property_runtime_errors_count_as_failed_cases():
    source = """
    def f (x : Int) : Bool := ?hole;
    @property(4)
    def prop_crashes (x : Int) : Bool := ignored := f x; native "1 / 0";
    """
    core, _, ectx, _, _, hole_name, corpora = _corpora(source)
    fitness = make_property_fitness(corpora[0], ectx)

    assert fitness(make_program(core, hole_name)(Literal(True, t_bool))) == 4.0


def test_synthesis_receives_minimized_property_goal_and_uses_its_fitness():
    source = """
    def f (x : Int) : Bool := ?hole;
    @property(8)
    def prop_f (x : Int) : Bool := f x;
    """
    core, ctx, ectx, metadata = check_and_return_core(source)
    targets = incomplete_functions_and_holes(ctx, core)
    synthesizer = _PropertySelectingSynthesizer()

    mapping = synthesize_holes(
        ctx,
        ectx,
        core,
        targets,
        metadata,
        synthesizer,
        budget=1,
        ui=SilentSynthesisUI(),
    )

    assert list(mapping.values()) == [Literal(True, t_bool)]
    assert synthesizer.seen_scores == [[8.0], [0.0]]
    assert len(synthesizer.seen_goals) == 1
    assert synthesizer.seen_goals[0].kind == "property"
    assert synthesizer.seen_goals[0].minimize is True


def test_property_goal_composes_after_existing_objectives():
    source = """
    @minimize_int(if f 0 then 0 else 1)
    def f (x : Int) : Bool := ?hole;
    @property(5)
    def prop_f (x : Int) : Bool := f x;
    """
    core, ctx, ectx, metadata = check_and_return_core(source)
    targets = incomplete_functions_and_holes(ctx, core)
    synthesizer = _PropertySelectingSynthesizer()

    synthesize_holes(ctx, ectx, core, targets, metadata, synthesizer, budget=1, ui=SilentSynthesisUI())

    assert [goal.kind for goal in synthesizer.seen_goals] == ["expression", "property"]
    assert synthesizer.seen_scores == [[1, 5.0], [0, 0.0]]


def test_gp_candidate_satisfies_property_fitness():
    source = """
    def f (x : Int) : Bool := ?hole;
    @property(6)
    def prop_f (x : Int) : Bool := f x;
    """
    core, ctx, ectx, metadata = check_and_return_core(source)
    targets = incomplete_functions_and_holes(ctx, core)
    mapping = synthesize_holes(
        ctx,
        ectx,
        core,
        targets,
        metadata,
        GESynthesizer(method="enumerative"),
        budget=0.5,
        ui=SilentSynthesisUI(),
    )
    filled = core
    for hole_name, candidate in mapping.items():
        assert candidate is not None
        filled = substitution(filled, candidate, hole_name)

    results = run_properties(ctx, ectx, filled, metadata)
    assert results and all(result.passed for result in results)


def test_adt_property_corpus_uses_constructor_values():
    source = """
    open Maybe
    def f (m : (Maybe Int)) : Bool := ?hole;
    @property(10)
    def prop_f (m : (Maybe Int)) : Bool := f m;
    """
    driver = AeonDriver(
        AeonConfig(synthesizer="enumerative", synthesis_ui=SilentSynthesisUI(), synthesis_budget=1, no_main=True)
    )
    assert driver.parse(aeon_code=source, filename="<property-fitness-test>") == []
    targets = incomplete_functions_and_holes(driver.typing_ctx, driver.core)
    fun_name, _ = targets[0]
    corpora = property_corpora_for_target(
        driver.typing_ctx,
        driver.core,
        driver.metadata,
        fun_name,
        {name for name, _ in targets},
        constructor_names=driver.constructor_names,
    )

    assert len(corpora) == 1
    rendered = [repr(case[0]).lower() for case in corpora[0].cases]
    assert all("maybe_just" in value or "maybe_none" in value for value in rendered)
    assert any("maybe_just" in value for value in rendered)
