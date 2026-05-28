"""Unit tests for the knee-point Pareto-front selector used by `GESynthesizer`."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from geneticengine.problems import Fitness, MultiObjectiveProblem

from aeon.synthesis.grammar.ge_synthesis import _knee_point_individual


@dataclass
class _StubIndividual:
    """Minimal Individual stand-in: holds a `Fitness` and returns it from `get_fitness`."""

    fitness: Fitness

    def get_fitness(self, problem: Any) -> Fitness:
        return self.fitness


def _make_problem(minimize: list[bool]) -> MultiObjectiveProblem:
    return MultiObjectiveProblem(
        fitness_function=lambda _phenotype: [0.0] * len(minimize),
        minimize=minimize,
    )


def _ind(*components: float) -> _StubIndividual:
    return _StubIndividual(Fitness(list(components), valid=True))


def _invalid() -> _StubIndividual:
    return _StubIndividual(Fitness([0.0], valid=False))


# ---------------------------------------------------------------------------
# Empty / invalid inputs
# ---------------------------------------------------------------------------


def test_empty_returns_none():
    assert _knee_point_individual([], _make_problem([True])) is None


def test_all_invalid_returns_none():
    problem = _make_problem([True, True])
    assert _knee_point_individual([_invalid(), _invalid()], problem) is None


def test_none_entries_are_skipped():
    problem = _make_problem([True, True])
    only_valid = _ind(1.0, 1.0)
    chosen = _knee_point_individual([None, only_valid, None], problem)
    assert chosen is only_valid


# ---------------------------------------------------------------------------
# Trivial cases
# ---------------------------------------------------------------------------


def test_single_valid_returned_directly():
    problem = _make_problem([True, True])
    only = _ind(5.0, 7.0)
    assert _knee_point_individual([only], problem) is only


def test_single_objective_minimize_picks_smallest():
    problem = _make_problem([True])
    pop = [_ind(10.0), _ind(3.0), _ind(7.0)]
    assert _knee_point_individual(pop, problem).fitness.fitness_components == [3.0]


def test_single_objective_maximize_picks_largest():
    problem = _make_problem([False])
    pop = [_ind(10.0), _ind(3.0), _ind(7.0)]
    assert _knee_point_individual(pop, problem).fitness.fitness_components == [10.0]


# ---------------------------------------------------------------------------
# Multi-objective knee selection
# ---------------------------------------------------------------------------


def test_balanced_point_beats_extremes_two_objective():
    """Front: (0, 10), (5, 5), (10, 0). Knee is the middle, closest to utopia (0, 0)."""
    problem = _make_problem([True, True])
    extremes_and_knee = [_ind(0.0, 10.0), _ind(5.0, 5.0), _ind(10.0, 0.0)]
    chosen = _knee_point_individual(extremes_and_knee, problem)
    assert chosen.fitness.fitness_components == [5.0, 5.0]


def test_maximize_objectives_are_oriented_correctly():
    """Mixed direction: minimize obj0, maximize obj1.
    Front: (0, 0)  -- worst on obj1
           (5, 5)  -- balanced
           (10, 10)-- worst on obj0
    Best obj0 = 0, best obj1 = 10. Utopia point (oriented to min) is (0, -10).
    Distances (normalized):
      (0, 0)   -> (0.0, 1.0)  -> 1.0
      (5, 5)   -> (0.5, 0.5)  -> 0.5
      (10, 10) -> (1.0, 0.0)  -> 1.0
    Knee is (5, 5).
    """
    problem = _make_problem([True, False])
    pop = [_ind(0.0, 0.0), _ind(5.0, 5.0), _ind(10.0, 10.0)]
    chosen = _knee_point_individual(pop, problem)
    assert chosen.fitness.fitness_components == [5.0, 5.0]


def test_zero_spread_dimension_is_ignored():
    """One dim flat across the front: contributes zero to distance; selection
    reduces to the active dimension."""
    problem = _make_problem([True, True])
    pop = [_ind(1.0, 5.0), _ind(3.0, 5.0), _ind(8.0, 5.0)]
    chosen = _knee_point_individual(pop, problem)
    # All have obj1 == 5 (flat); knee == smallest obj0.
    assert chosen.fitness.fitness_components == [1.0, 5.0]


def test_invalid_individuals_filtered_out():
    """Invalid candidates must not skew the normalization range."""
    problem = _make_problem([True, True])
    pop = [_invalid(), _ind(0.0, 10.0), _ind(5.0, 5.0), _ind(10.0, 0.0), _invalid()]
    chosen = _knee_point_individual(pop, problem)
    assert chosen.fitness.fitness_components == [5.0, 5.0]
