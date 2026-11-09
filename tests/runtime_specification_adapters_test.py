"""Runtime goals compose with solver and noisy-learning specifications."""

import pytest

from aeon.core.terms import Literal, Var
from aeon.core.types import t_int
from aeon.synthesis.api import InvalidIndividualException
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.modules.noisy import NoisySynthesizer
from aeon.synthesis.modules.noisy.model import Config
from aeon.synthesis.modules.ortools_cpsat import CPSatHoleSynthesizer
from aeon.synthesis.program_specifications import ProgramSpecifications
from tests.joint_hole_synthesis_test import parse, solve


def install_resource_meters(monkeypatch):
    from aeon.synthesis import fitness_eval

    monkeypatch.setattr(fitness_eval, "measure_cputime", lambda thunk: float(thunk()) + 0.25)
    monkeypatch.setattr(fitness_eval, "measure_energy", lambda thunk: 3.0 - float(thunk()))


def test_program_specifications_check_completeness_and_mixed_objective_order(monkeypatch):
    install_resource_meters(monkeypatch)
    driver = parse("""
        @example(f >= 1)
        @minimize_size
        @minimize_cputime(f)
        @minimize_energy(f)
        @maximize_int(f)
        def f:{v:Int | 0 <= v && v <= 2} := ?h;
        @property(3) def positive(x:Int):Bool := f > 0;
    """)
    targets = incomplete_functions_and_holes(driver.typing_ctx, driver.core)
    hole = targets[0][1][0]
    with ProgramSpecifications(
        driver.typing_ctx, driver.evaluation_ctx, driver.core, targets, driver.metadata
    ) as specs:
        with pytest.raises(InvalidIndividualException, match="every"):
            specs.candidate({})
        assert not specs.validate(specs.candidate({hole: Literal(0, t_int)}))
        good = specs.candidate({hole: Literal(1, t_int)})
        assert specs.validate(good)
        assert specs.evaluate(good) == [0.0, 1.0, 1.25, 2.0, 1.0, 0.0]
        assert specs.mapping(good) == {hole: Literal(1, t_int)}


def test_cpsat_collects_pareto_front_with_size_resources_examples_and_properties(monkeypatch):
    pytest.importorskip("ortools")
    install_resource_meters(monkeypatch)
    driver = parse("""
        @example(f >= 1)
        @minimize_size
        @minimize_cputime(f)
        @minimize_energy(f)
        @maximize_int(f)
        def f:{v:Int | 0 <= v && v <= 2} := ?h;
        @property(3) def positive(x:Int):Bool := f > 0;
    """)
    backend = CPSatHoleSynthesizer(bound=2)
    result = solve(driver, backend, 4)
    assert next(iter(result.values())).value in {1, 2}
    assert {candidate.terms[0].value for _, candidate in backend.pareto_front} == {1, 2}
    assert all(scores[0] == scores[-1] == 0 for scores, _ in backend.pareto_front)


def test_cpsat_uses_runtime_objective_when_symbolic_translation_is_unavailable():
    pytest.importorskip("ortools")
    driver = parse("""
        def x:{v:Int | 1 <= v && v <= 2} := ?hx;
        def y:{v:Int | 1 <= v && v <= 2} := ?hy;
        @minimize_int(x / y)
        def cost:Int := x / y;
    """)
    backend = CPSatHoleSynthesizer(bound=2)
    result = solve(driver, backend, 4)
    assert {hole.name: term.value for hole, term in result.items()} == {"hx": 1, "hy": 2}
    # Int division uses Euclidean quotient semantics, so 1 / 2 scores zero.
    assert backend.pareto_front[0][0] == [0.0]


def test_cpsat_property_rejection_continues_to_next_assignment():
    pytest.importorskip("ortools")
    driver = parse("""
        def f:{v:Int | 0 <= v && v <= 2} := ?h;
        @property(3) def choose(x:Int):Bool := f = 2;
    """)
    result = solve(driver, CPSatHoleSynthesizer(bound=2), 4)
    assert next(iter(result.values())) == Literal(2, t_int)


def test_cpsat_type_only_specification_needs_no_objective():
    pytest.importorskip("ortools")
    driver = parse("def f:{v:Int | v = 2} := ?h;")
    assert next(iter(solve(driver, CPSatHoleSynthesizer(), 2).values())) == Literal(2, t_int)


def test_cpsat_csv_remains_regression_when_combined_with_size():
    pytest.importorskip("ortools")
    driver = parse(r"""
        @csv_data("0.0,0.0\n0.0,1.0")
        @minimize_size
        def f(x:Float):{v:Float | 0.0 <= v && v <= 1.0} := ?h;
    """)
    result = solve(driver, CPSatHoleSynthesizer(bound=1, scale=2), 4)
    assert next(iter(result.values())).value == 0.5


def noisy_candidates(monkeypatch, values):
    import aeon.synthesis.modules.noisy as noisy

    monkeypatch.setattr(noisy, "iter_candidates", lambda *args, **kwargs: iter(values))


def test_noisy_property_is_hard_while_contradictory_example_stays_soft(monkeypatch):
    driver = parse("""
        @example(f 0 = 1)
        def f(x:Int):Int := ?h;
        @property(5) def identity(x:Int):Bool := f x = x;
    """)
    function = next(name for name in driver.metadata if name.name == "f")
    x = driver.metadata[function]["io_params"][0]
    noisy_candidates(monkeypatch, [Literal(1, t_int), Var(x)])
    backend = NoisySynthesizer(config=Config(regularization=0))
    result = solve(driver, backend, 4)
    assert next(iter(result.values())) == Var(x)
    assert backend.last_report.empirical_error == 1
    assert backend.last_report.invalid_candidates >= 1


def test_noisy_resource_and_numeric_goals_rank_fully_scored_candidates(monkeypatch):
    install_resource_meters(monkeypatch)
    driver = parse("""
        @example(f 0 = 0)
        @minimize_size
        @minimize_cputime(f 0)
        @minimize_energy(f 0)
        @maximize_int(f 0)
        def f(x:Int):{v:Int | 0 <= v && v <= 1} := ?h;
    """)
    noisy_candidates(monkeypatch, [Literal(0, t_int), Literal(1, t_int)])
    backend = NoisySynthesizer(config=Config(regularization=0))
    result = solve(driver, backend, 4)
    assert next(iter(result.values())).value in {0, 1}
    assert {term.value for _, term in backend.pareto_front} == {0, 1}
    assert sorted(scores for scores, _ in backend.pareto_front) == [
        [0.0, 1.0, 0.25, 3.0, 0.0],
        [1.0, 1.0, 1.25, 2.0, 1.0],
    ]
    assert backend.last_report.candidates_fully_scored == 2


@pytest.mark.parametrize("file", [False, True])
def test_noisy_accepts_both_csv_forms_without_requiring_an_exact_fit(monkeypatch, tmp_path, file):
    csv = tmp_path / "noisy.csv"
    csv.write_text("0,0\n0,1\n")
    decorator = f'@csv_file("{csv}")' if file else r'@csv_data("0,0\n0,1")'
    driver = parse(decorator + " def f(x:Int):Int := ?h;")
    noisy_candidates(monkeypatch, [Literal(0, t_int), Literal(1, t_int)])
    backend = NoisySynthesizer(config=Config(regularization=0))
    result = solve(driver, backend, 4)
    assert next(iter(result.values())).value in {0, 1}
    assert backend.last_report.empirical_error == 0.5


def test_noisy_drops_candidates_whose_additional_objective_has_no_value():
    from aeon.synthesis.modules.noisy.model import Dataset
    from aeon.synthesis.modules.noisy.search import run_search
    from aeon.synthesis.uis.api import SilentSynthesisUI

    published = []
    result, report = run_search(
        Dataset.from_pairs([([], 1)], 0),
        Config(regularization=0),
        0,
        iter([Literal(0, t_int), Literal(1, t_int)]),
        lambda _: True,
        lambda term, _: term.value,
        set(),
        {},
        SilentSynthesisUI(),
        2,
        objectives=lambda term: [1 / (1 - term.value)],
        objective_directions=[True],
        on_front=lambda front: published.append(front),
    )
    assert result == Literal(0, t_int)
    assert report.candidates_fully_scored == 1
    assert report.invalid_candidates == 1
    assert all(term == result for front in published for _, term in front)


def test_decision_tree_scores_nullary_training_data_and_publishes_the_front():
    from aeon.synthesis.modules.decision_tree import DecisionTreeSynthesizer

    driver = parse("""
        @example(f = 0)
        @example(f = 2)
        @maximize_int(f)
        @minimize_size
        def f:Int := ?h;
    """)
    backend = DecisionTreeSynthesizer()
    result = solve(driver, backend, 2)
    assert next(iter(result.values())).value in {0, 2}
    assert {term.value for _, term in backend.pareto_front} == {0, 2}
    assert all(scores[-1] == 1.0 for scores, _ in backend.pareto_front)
