"""Noisy observations are soft; contracts, execution and complete scoring are hard."""

from dataclasses import replace
from itertools import combinations
import math
import random
from time import monotonic, sleep

import pytest

from aeon.backend.evaluator import EvaluationContext, eval as aeon_eval
from aeon.compilation.session import CompilationSession
from aeon.core.terms import Abstraction, Annotation, Application, Hole, If, Literal, TypeApplication, Var
from aeon.core.types import t_bool, t_int
from aeon.prelude.prelude import evaluation_vars
from aeon.synthesis.api import InvalidIndividualException, SynthesisNotSuccessful, UnsupportedSynthesisGoal
from aeon.synthesis.modules.noisy import NoisySynthesizer
from aeon.synthesis.modules.noisy.model import Config, Dataset, same_value
from aeon.synthesis.modules.noisy.sampling import discrepancy, select_sample
from aeon.synthesis.modules.noisy.search import run_search
from aeon.synthesis.modules.noisy.structure import complexity, identity
from aeon.synthesis.pbt import run_examples
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.synthesis.fitness_eval import set_program_tail
from aeon.synthesis.identification import iterate_top_level
from aeon.utils.name import Name
from tests.joint_hole_synthesis_test import parse, solve, fill


@pytest.fixture(autouse=True)
def session():
    with CompilationSession().activate():
        yield


X = Name("x", 100)


def integer(value):
    return Literal(value, t_int)


def op(name, left, right):
    return Application(Application(TypeApplication(Var(Name(name, 0)), t_int), left), right)


def evaluate(term, values):
    return aeon_eval(term, EvaluationContext(evaluation_vars).with_var(X, values[0]))


def search(terms, rows=None, *, config=None, validate=lambda t: True, probe=evaluate, budget=2):
    dataset = Dataset.from_pairs(rows or [([1], 2), ([2], 4), ([3], 6), ([4], 999)], 1)
    return run_search(
        dataset,
        config or Config(candidates_per_round=4),
        0,
        iter(terms),
        validate,
        probe,
        {X},
        {},
        SilentSynthesisUI(),
        budget,
    )


def doubling_candidates():
    simple = op("*", integer(2), Var(X))
    overfit = If(op("==", Var(X), integer(4)), integer(999), simple)
    return simple, overfit


def test_regularization_controls_ranking_by_the_declared_formula():
    simple, overfit = doubling_candidates()
    difference = complexity(overfit, {X}, {}) - complexity(simple, {X}, {})
    threshold = 0.25 / difference
    perfect, low = search([simple, overfit], config=Config(regularization=threshold / 2))
    smaller, high = search([simple, overfit], config=Config(regularization=threshold * 2))
    assert perfect == overfit and low.empirical_error == 0
    assert smaller == simple and high.empirical_error == 0.25
    assert high.objective == high.empirical_error + high.regularization_term
    assert high.residuals[0].observation_id == 3
    assert (high.residuals[0].expected, high.residuals[0].actual) == (999, 8)


def test_validation_precedes_any_observation_and_invalid_high_fit_cannot_win():
    simple, overfit = doubling_candidates()
    seen = set()

    def validate(term):
        seen.add(identity(term))
        return term == simple

    def observe(term, values):
        assert identity(term) in seen
        assert term != overfit, "refinement-invalid candidate was evaluated"
        return evaluate(term, values)

    term, report = search([overfit, simple], validate=validate, probe=observe, config=Config(regularization=0))
    assert term == simple
    assert report.invalid_candidates == 1
    assert report.empirical_error == 0.25


def test_duplicate_contradictory_rows_remain_distinct():
    term, report = search([Var(X)], rows=[([2], 2), ([2], 999), ([2], 999)])
    assert term == Var(X)
    assert report.row_count == 3 and report.empirical_error == 2 / 3
    assert [r.observation_id for r in report.residuals] == [1, 2]
    assert report.row_evaluations == 3
    assert same_value(True, 1) is False


@pytest.mark.parametrize(
    "pairs", [[], [([math.nan], 1)], [([1], math.inf)], [([1], (1, 2))], [(1, 2)], [([1, 2], 3)], [([1],)]]
)
def test_malformed_or_nonfinite_dataset_rejected(pairs):
    with pytest.raises(UnsupportedSynthesisGoal):
        Dataset.from_pairs(pairs, 1)


@pytest.mark.parametrize("regularization", [-1, math.inf, math.nan])
def test_invalid_regularization_rejected(regularization):
    with pytest.raises(UnsupportedSynthesisGoal):
        Config(regularization=regularization)


def test_alpha_stable_complexity_and_helpers_are_not_free():
    a, b, helper = Name("a", 1), Name("renamed", 2), Name("helper", 3)
    first, second = Abstraction(a, op("+", Var(a), integer(1))), Abstraction(b, op("+", Var(b), integer(1)))
    assert identity(first) == identity(second)
    assert complexity(first, set(), {}) == complexity(second, set(), {})
    assert complexity(Var(helper), set(), {helper: first}) == 1 + complexity(first, set(), {})
    with pytest.raises(InvalidIndividualException):
        complexity(Var(helper), set(), {})
    with pytest.raises(InvalidIndividualException):
        complexity(Var(helper), set(), {helper: Var(helper)})


def test_exact_sampler_uses_more_than_latest_candidate_and_matches_oracle():
    history = ((0, 0, 1, 1), (0, 1, 0, 1))
    config = Config()
    selected = select_sample(history, 4, 2, random.Random(7), config, monotonic() + 2)
    oracle = min((discrepancy(history, subset, 4), subset) for subset in combinations(range(4), 2))
    assert (selected.discrepancy, selected.sample) == oracle
    assert selected.method == "exact" and selected.history_count == 2
    latest = select_sample(history[-1:], 4, 2, random.Random(7), config, monotonic() + 2)
    assert latest.sample != selected.sample
    assert discrepancy(history, latest.sample, 4) > selected.discrepancy


def test_heuristic_and_uniform_samplers_are_seeded_and_reported():
    history = ((0, 0, 0, 1, 1, 1), (0, 1, 0, 1, 0, 1))
    config = Config(exact_subsets=1)
    one = select_sample(history, 6, 3, random.Random(5), config, monotonic() + 2)
    two = select_sample(history, 6, 3, random.Random(5), config, monotonic() + 2)
    assert one == two and "heuristic" in one.method
    uniform = select_sample(history, 6, 3, random.Random(5), replace(config, sampler="uniform"), monotonic() + 2)
    assert uniform.method == "uniform"
    assert one.discrepancy <= uniform.discrepancy


def test_samples_grow_and_full_data_score_selects_incumbent():
    rows = [([i], i) for i in range(8)]
    # Seed zero initially samples row 6. Constant six fits that sample perfectly
    # but must lose on the full dataset to identity.
    term, report = search([integer(6), Var(X)], rows=rows, config=Config(initial_sample=1))
    assert term == Var(X) and report.empirical_error == 0
    assert [len(r.sample) for r in report.rounds] == [1, 2, 4, 8]
    assert report.rounds[-1].method == "full"
    assert max(r.history_count for r in report.rounds) >= 2


def test_candidate_crash_is_invalid_not_a_noisy_row():
    def observe(term, values):
        if term == integer(999):
            raise ZeroDivisionError()
        return evaluate(term, values)

    term, report = search([integer(999), Var(X)], rows=[([1], 1), ([2], 2)], probe=observe)
    assert term == Var(X) and not report.residuals
    assert report.invalid_candidates == 1


def test_timed_out_candidate_cannot_displace_completed_incumbent():
    def observe(term, values):
        if term == integer(999):
            sleep(1)
        return evaluate(term, values)

    started = monotonic()
    term, report = search(
        [Var(X), integer(999)],
        rows=[([i], i) for i in range(8)],
        probe=observe,
        config=Config(initial_sample=1, candidates_per_round=1, call_timeout=0.05),
    )
    assert monotonic() - started < 1
    assert term == Var(X) and report.stop_reason == "worker_timeout"
    assert report.invalid_candidates == 1 and not report.residuals


def test_budget_expiry_keeps_incumbent_or_fails_without_one():
    def stream():
        yield Var(X)
        sleep(1)

    dataset = Dataset.from_pairs([([i], i) for i in range(8)], 1)
    term, report = run_search(
        dataset,
        Config(initial_sample=1, candidates_per_round=1, call_timeout=2),
        0,
        stream(),
        lambda _: True,
        evaluate,
        {X},
        {},
        SilentSynthesisUI(),
        0.15,
    )
    assert term == Var(X) and report.stop_reason == "budget"
    with pytest.raises(SynthesisNotSuccessful, match="no validated"):
        search([Var(X)], budget=0)


def source(precise=False):
    result = "v = x" if precise else "v >= 0"
    return f"""@example(f 0 = 0) @example(f 1 = 1) @example(f 2 = 2) @example(f 3 = 99)
    def f(x:{{u:Int | u >= 0}}):{{v:Int | {result}}} := ?h;"""


@pytest.mark.parametrize("precise", [False, True])
def test_real_compiler_search_heldout_execution_and_example_failures(precise):
    driver = parse(source(precise))
    before = repr(driver.metadata)
    engine = NoisySynthesizer(config=Config(candidates_per_round=8))
    completed = fill(driver, solve(driver, engine, budget=5))
    assert engine.last_report.empirical_error == 0.25
    assert repr(driver.metadata) == before
    name = next(r.var_name for r in iterate_top_level(completed) if r.var_name.name == "f")
    for value in (4, 10, 50):
        result = aeon_eval(set_program_tail(completed, Application(Var(name), integer(value))), driver.evaluation_ctx)
        assert result == value
    results = run_examples(driver.evaluation_ctx, completed, driver.metadata)
    assert sum(not r.passed for r in results) == 1


def test_real_precise_contract_rejects_overfitting_before_acceptance(monkeypatch):
    import aeon.synthesis.modules.noisy as module

    driver = parse(source(True))

    def candidates(ctx, *args, **kwargs):
        x = next(n for n, _ in ctx.concrete_vars() if n.name == "x")
        yield If(op("==", Var(x), integer(3)), integer(99), Var(x))
        yield Var(x)

    monkeypatch.setattr(module, "iter_candidates", candidates)
    engine = NoisySynthesizer(config=Config(regularization=0))
    fill(driver, solve(driver, engine, 3))
    assert engine.last_report.empirical_error == 0.25
    assert engine.last_report.invalid_candidates >= 1


@pytest.mark.parametrize(
    "code",
    [
        "def f(x:Int):Int := ?h;",
        "@example(f 0 > 1) def f(x:Int):Int := ?h;",
        "@example(f 0 = 1) @minimize_int(f 1) def f(x:Int):Int := ?h;",
        "@example(f 0 = 1) def f(x:Int):Int := ?h; @property(1) def p(x:Int):Bool := f x = x;",
        "@example(f 0 = 1) def f(x:Int):Int := ?h; def g:Int := ?hg;",
        "@example(f 0 = 1) def f(x:Int):Int := if true then ?a else ?b;",
    ],
)
def test_unsupported_goals_are_explicit(code):
    driver = parse(code)
    with pytest.raises(UnsupportedSynthesisGoal):
        solve(driver, NoisySynthesizer(), 1)


def test_wrong_scalar_types_and_out_of_domain_inputs_are_rejected():
    driver = parse(source())
    key = next(k for k in driver.metadata if k.name == "f")
    driver.metadata[key]["io_examples"][0] = ([True], 0)
    with pytest.raises(UnsupportedSynthesisGoal, match="type mismatch"):
        solve(driver, NoisySynthesizer(), 1)
    driver.metadata[key]["io_examples"][0] = ([-1], 0)
    with pytest.raises(UnsupportedSynthesisGoal, match="precondition"):
        solve(driver, NoisySynthesizer(), 1)


def test_registration_environment_and_report_summary(monkeypatch, capsys):
    from aeon.lsp.server import SYNTHESIZERS
    from aeon.synthesis.modules.synthesizerfactory import make_synthesizer, synthesizer_family, SynthesizerFamily
    from aeon.synthesis.uis.terminal import TerminalUI

    monkeypatch.setenv("AEON_SEED", "21")
    monkeypatch.setenv("AEON_NOISY_LAMBDA", "0.125")
    backend = make_synthesizer("noisy")
    assert backend.seed == 21 and backend.config.regularization == 0.125
    assert synthesizer_family("noisy") == SynthesizerFamily.EXAMPLE_DRIVEN and "noisy" in SYNTHESIZERS
    _, report = search([Var(X)], rows=[([1], 1), ([2], 3)])
    TerminalUI().report(report.as_dict())
    text = capsys.readouterr().out
    assert "1/2 residuals" in text and "score=" in text


def test_partial_candidates_and_wrong_runtime_types_cannot_win():
    def observe(term, values):
        return True if term == integer(1) else evaluate(term, values)

    term, report = search([Hole(Name("unfinished", 1)), integer(1), Var(X)], rows=[([1], 1), ([2], 2)], probe=observe)
    assert term == Var(X)
    assert report.invalid_candidates == 2 and not report.residuals


def test_validation_cache_retains_type_annotations():
    invalid = Annotation(Var(X), t_bool)
    assert complexity(invalid, {X}, {}) == complexity(Var(X), {X}, {})
    assert identity(invalid) != identity(Var(X))
    term, report = search([invalid, Var(X)], rows=[([1], 1)], validate=lambda term: term == Var(X))
    assert term == Var(X) and report.invalid_candidates == 1


def test_lexical_captures_keep_their_scope_and_pay_for_their_definitions():
    driver = parse("""
    @example(f 0 = 1) @example(f 1 = 2) @example(f 2 = 3)
    def f(x:Int):Int := let captured := x + 1 in ?h;
    """)
    engine = NoisySynthesizer(config=Config(candidates_per_round=8))
    completed = fill(driver, solve(driver, engine, 5))
    assert not engine.last_report.residuals
    assert engine.last_report.complexity > 1
    name = next(r.var_name for r in iterate_top_level(completed) if r.var_name.name == "f")
    assert aeon_eval(set_program_tail(completed, Application(Var(name), integer(20))), driver.evaluation_ctx) == 21


def test_seeded_runs_have_independent_caches_and_deterministic_samples():
    rows = [([i], i) for i in range(8)]
    terms = [integer(0), Var(X), integer(2)]
    first, one = search(terms, rows=rows, config=Config(initial_sample=1))
    second, two = search(terms, rows=rows, config=Config(initial_sample=1))
    assert first == second
    assert one.rounds == two.rounds
    assert one.row_evaluations == two.row_evaluations
    assert one.candidates_validated == two.candidates_validated
