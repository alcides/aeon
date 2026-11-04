"""GP selection must respect trade-offs instead of prioritizing objective order."""

import random

import pytest

from aeon.core.terms import Literal
from aeon.core.types import t_int
from aeon.synthesis.decorators import Goal
from aeon.synthesis.modules import genetic_programming as gp
from aeon.synthesis.modules.native_search import initial_partial
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def individual(index, fitness, valid=True):
    return gp.Individual([index], Literal(index, t_int), fitness, valid)


def mixed_population():
    # Minimize the first component, maximize the second. First two trade off;
    # the next two form rank 1, and the fifth is dominated by both rank-1 points.
    return [
        individual(0, [1, 5]),
        individual(1, [2, 8]),
        individual(2, [2, 4]),
        individual(3, [3, 7]),
        individual(4, [4, 3]),
        individual(5, [1, 5]),  # Equal fitness retains a separate eligible genome.
        individual(6, [-100, 100], valid=False),
        individual(7, None),
    ]


def test_ranks_respect_mixed_directions_ties_and_validity():
    assert gp._pareto_ranks(mixed_population(), [True, False]) == [0, 0, 1, 1, 2, 0, 3, 3]


@pytest.mark.parametrize("directions", [[True, False], [True, True], [False, False]])
def test_tournaments_can_choose_every_best_tradeoff_and_never_a_dominated_point(directions):
    # Convert a common all-minimize trade-off to each requested orientation.
    scores = [[0, 10], [10, 0], [20, 20]]
    population = [
        individual(i, [v if minimize else -v for v, minimize in zip(score, directions)])
        for i, score in enumerate(scores)
    ]
    winners = {
        gp.tournament_select(random.Random(seed), population, len(population), directions).genome[0]
        for seed in range(32)
    }
    assert winners == {0, 1}


def test_tournament_chooses_the_best_rank_present_in_its_sample():
    population = mixed_population()

    class Subset(random.Random):
        def sample(self, population, k):
            return [2, 4, 6]  # No rank-0 individuals participate.

    assert gp.tournament_select(Subset(0), population, 3, [True, False]) is population[2]


def test_elites_take_complete_fronts_before_filling_from_the_next_front():
    population = mixed_population()
    for seed in range(16):
        selected = gp.select_elites(random.Random(seed), population, 4, [True, False])
        indices = [ind.genome[0] for ind in selected]
        assert set(indices[:3]) == {0, 1, 5}
        assert indices[3] in {2, 3}
        assert len(set(indices)) == 4


def test_elite_cutoff_does_not_always_favor_the_first_objective_or_duplicate():
    population = mixed_population()
    selected = {gp.select_elites(random.Random(seed), population, 1, [True, False])[0].genome[0] for seed in range(32)}
    assert selected == {0, 1, 5}


def test_selection_is_seeded_and_invariant_under_objective_permutation():
    population = mixed_population()
    permuted = [individual(ind.genome[0], ind.fitness[::-1] if ind.fitness else None, ind.valid) for ind in population]
    for seed in range(16):
        winner = gp.tournament_select(random.Random(seed), population, 5, [True, False])
        repeated = gp.tournament_select(random.Random(seed), population, 5, [True, False])
        reordered = gp.tournament_select(random.Random(seed), permuted, 5, [False, True])
        assert winner.genome == repeated.genome == reordered.genome
        elites = gp.select_elites(random.Random(seed), population, 4, [True, False])
        repeated_elites = gp.select_elites(random.Random(seed), population, 4, [True, False])
        reordered_elites = gp.select_elites(random.Random(seed), permuted, 4, [False, True])
        assert [i.genome for i in elites] == [i.genome for i in repeated_elites] == [i.genome for i in reordered_elites]


def test_invalid_population_remains_selectable_without_fitness_comparisons():
    population = [individual(0, None), individual(1, [-100, 100], valid=False)]
    assert gp._pareto_ranks(population, [True, False]) == [0, 0]
    winners = {gp.tournament_select(random.Random(seed), population, 2, [True, False]).genome[0] for seed in range(16)}
    assert winners == {0, 1}
    assert len(gp.select_elites(random.Random(0), population, 10, [True, False])) == 2
    assert gp.select_elites(random.Random(0), population, 0, [True, False]) == []
    assert gp.select_elites(random.Random(0), [], 1, [True, False]) == []


@pytest.mark.parametrize("minimize, expected", [(True, [1, 2, 0]), (False, [0, 2, 1])])
def test_single_objective_selection_keeps_scalar_order_and_random_state(minimize, expected):
    population = [individual(0, [9]), individual(1, [1]), individual(2, [5]), individual(3, None)]
    rng = random.Random(17)
    state = rng.getstate()
    elites = gp.select_elites(rng, population, 3, [minimize])
    assert [ind.genome[0] for ind in elites] == expected
    assert rng.getstate() == state  # No additional tie-breaking draws for scalar elitism.
    assert gp.tournament_select(rng, population, len(population), [minimize]) is population[expected[0]]


def test_multi_component_goal_uses_one_ranking_per_generation(monkeypatch):
    monkeypatch.setattr(gp, "PROBE_INDIVIDUALS", 4)
    # The assessment cap makes this integration check independent of clock speed.
    monkeypatch.setattr(gp, "monotonic", lambda: 0.0)
    rank_populations = []
    tournament_populations = []
    elite_populations = []
    original_ranks = gp._pareto_ranks
    original_tournament = gp.tournament_select
    original_elites = gp.select_elites

    def ranking(population, minimize):
        rank_populations.append(population)
        return original_ranks(population, minimize)

    def tournament(rng, population, k, minimize, *, ranks=None):
        assert minimize == [True, True]
        assert ranks is not None
        tournament_populations.append(population)
        return original_tournament(rng, population, k, minimize, ranks=ranks)

    def elites(rng, population, count, minimize, *, ranks=None):
        assert ranks is not None
        elite_populations.append(population)
        return original_elites(rng, population, count, minimize, ranks=ranks)

    monkeypatch.setattr(gp, "_pareto_ranks", ranking)
    monkeypatch.setattr(gp, "tournament_select", tournament)
    monkeypatch.setattr(gp, "select_elites", elites)
    name = Name("f", 0)
    metadata = {name: {"goals": [Goal(True, 2, name)]}}  # One decorator, two objectives.
    result = gp.GeneticProgrammingSynthesizer(seed=0)._search(
        initial_partial(TypingContext(), t_int),
        lambda _: False,
        lambda _: True,
        lambda term: [float(term.value), float(255 - term.value)],
        name,
        metadata,
        budget=1,
        ui=SilentSynthesisUI(),
        decode=lambda genome, generation: Literal(genome[0], t_int),
        max_assessments=12,
        population_size=4,
    )
    assert result is not None
    assert len(rank_populations) >= 2
    assert len(rank_populations) == len(elite_populations)
    assert len({id(population) for population in rank_populations}) == len(rank_populations)
    assert tournament_populations
    assert all(any(population is ranked for ranked in rank_populations) for population in tournament_populations)
