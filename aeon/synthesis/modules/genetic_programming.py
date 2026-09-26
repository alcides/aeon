"""Native genetic programming over Aeon's core term grammar.

Individuals are linear genomes: sequences of integer codons that select among
grammar expansions when mapping to a core term.  There is no fixed max depth —
deeper trees appear as longer genomes evolve.  Population size is set from a
timing probe of the first ten random individuals so that initial evaluation
uses at most 10% of the wall-clock budget.  Crossover rate, mutation rate and
other operator parameters are sampled randomly each run (and tournament sizes
are re-sampled every generation).

No GeneticEngine dependency.
"""

from __future__ import annotations

import math
import random
from collections.abc import Callable
from dataclasses import dataclass, field
from time import monotonic

from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import InvalidIndividualException, Synthesizer, TimeoutInEvaluationException
from aeon.synthesis.decorators import Goal
from aeon.synthesis.modules.native_search import (
    ParetoEntry,
    expansions_for_hole,
    initial_partial,
    literal_completions,
    make_skip,
    update_pareto_front,
)
from aeon.synthesis.modules.tdsyn.worklist import PartialAST
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name

CODON_SIZE = 256
PROBE_INDIVIDUALS = 10
INIT_BUDGET_FRACTION = 0.10
ELITISM_FRACTION = 0.05
MIN_POPULATION = 2
MAX_POPULATION = 500
# Soft cap on codon consumption per mapping so a single decode cannot loop forever
# when only recursive productions apply; raised with the generation index.
BASE_CHOICE_BUDGET = 32


Genome = list[int]


@dataclass
class Individual:
    genome: Genome
    term: Term | None = None
    fitness: list[float] | None = None
    valid: bool = False


@dataclass
class GPState:
    rng: random.Random
    minimize: list[bool]
    crossover_rate: float
    mutation_rate: float
    # Re-sampled every generation.
    tournament_size: int = 2
    mutation_codons: int = 1
    novelty_rate: float = 0.0
    generation: int = 0
    assessed: int = 0
    pareto_front: list[ParetoEntry] = field(default_factory=list)


def _random_genome(rng: random.Random, length: int) -> Genome:
    return [rng.randrange(CODON_SIZE) for _ in range(max(1, length))]


def map_genome(
    genome: Genome,
    initial: PartialAST,
    skip: Callable[[Name], bool],
    generation: int = 0,
) -> Term | None:
    """Decode a codon sequence into a complete term via grammar choices.

    Each codon selects among the expansions of the current leftmost hole.
    When the choice budget for this generation is exhausted, only terminal
    (closed) expansions are considered so the tree always finishes.  The
    budget grows with ``generation``, so later populations can express deeper
    terms without a fixed max depth.
    """
    if not genome:
        return None

    partial = PartialAST(initial.term, list(initial.holes), initial.depth)
    gene_i = 0
    wraps = 0
    choices_used = 0
    choice_budget = BASE_CHOICE_BUDGET * (1 + generation)

    while not partial.is_complete():
        completions = literal_completions(partial)
        if completions:
            codon = genome[gene_i % len(genome)]
            gene_i += 1
            if gene_i >= len(genome) * (wraps + 1):
                wraps += 1
            return completions[codon % len(completions)]

        hole = partial.holes[0]
        options = expansions_for_hole(partial, hole, skip, max_depth=None)
        if not options:
            return None

        force_terminal = choices_used >= choice_budget or wraps >= max(1, 1 + generation)
        if force_terminal:
            closed = [opt for opt in options if not opt.holes]
            if closed:
                options = closed
            elif choices_used >= choice_budget * 2:
                # Still no terminal: give up rather than diverge.
                return None

        codon = genome[gene_i % len(genome)]
        gene_i += 1
        if gene_i > 0 and gene_i % len(genome) == 0:
            wraps += 1
        choices_used += 1
        partial = options[codon % len(options)]

    return partial.term


def one_point_crossover(rng: random.Random, a: Genome, b: Genome) -> tuple[Genome, Genome]:
    if len(a) < 2 or len(b) < 2:
        return list(a), list(b)
    cut_a = rng.randrange(1, len(a))
    cut_b = rng.randrange(1, len(b))
    return a[:cut_a] + b[cut_b:], b[:cut_b] + a[cut_a:]


def mutate(rng: random.Random, genome: Genome, mutation_rate: float, mutation_codons: int) -> Genome:
    child = list(genome)
    # Point mutations.
    for i in range(len(child)):
        if rng.random() < mutation_rate:
            child[i] = rng.randrange(CODON_SIZE)
    # Structural growth / shrinkage so genomes (and thus trees) can deepen.
    if rng.random() < mutation_rate:
        for _ in range(max(1, mutation_codons)):
            op = rng.choice(("insert", "delete", "append"))
            if op == "insert":
                child.insert(rng.randrange(len(child) + 1), rng.randrange(CODON_SIZE))
            elif op == "append":
                child.append(rng.randrange(CODON_SIZE))
            elif op == "delete" and len(child) > 1:
                del child[rng.randrange(len(child))]
    return child if child else _random_genome(rng, 1)


def tournament_select(rng: random.Random, population: list[Individual], k: int, minimize: list[bool]) -> Individual:
    k = max(1, min(k, len(population)))
    contestants = rng.sample(population, k)
    return _best_individual(contestants, minimize)


def _fitness_key(fitness: list[float] | None, minimize: list[bool]) -> tuple:
    """Sort key: valid fitnesses first, then Pareto-friendly tuple (lower better)."""
    if fitness is None:
        return (1, ())
    oriented = tuple(v if is_min else -v for v, is_min in zip(fitness, minimize))
    return (0, oriented)


def _best_individual(population: list[Individual], minimize: list[bool]) -> Individual:
    valid = [ind for ind in population if ind.valid and ind.fitness is not None]
    pool = valid if valid else population
    return min(pool, key=lambda ind: _fitness_key(ind.fitness, minimize))


def _elite_count(pop_size: int) -> int:
    return max(1, int(math.ceil(pop_size * ELITISM_FRACTION))) if pop_size > 0 else 0


def choose_population_size(probe_seconds: float, budget: float, probe_n: int = PROBE_INDIVIDUALS) -> int:
    """Size the population so one full evaluation wave fits in 10% of ``budget``."""
    if probe_seconds <= 0 or budget <= 0:
        return MIN_POPULATION
    per_individual = probe_seconds / max(1, probe_n)
    init_allowance = budget * INIT_BUDGET_FRACTION
    # The probe already spent ``probe_seconds``; remaining init allowance buys more slots.
    remaining = max(0.0, init_allowance - probe_seconds)
    extra = int(remaining / per_individual) if per_individual > 0 else 0
    size = max(probe_n, probe_n + extra)
    # If the probe alone already exceeded 10%, keep the probed individuals only.
    if probe_seconds >= init_allowance:
        size = max(MIN_POPULATION, probe_n)
    return max(MIN_POPULATION, min(MAX_POPULATION, size))


def _assess(
    ind: Individual,
    initial: PartialAST,
    skip: Callable[[Name], bool],
    validate: Callable[[Term], bool],
    evaluate: Callable[[Term], list[float]],
    state: GPState,
    ui: SynthesisUI,
    started: float,
    budget: float,
) -> Term | None:
    """Map, validate and evaluate one individual. Return early term if no objectives."""
    term = map_genome(ind.genome, initial, skip, generation=state.generation)
    ind.term = term
    ind.fitness = None
    ind.valid = False
    state.assessed += 1

    if term is None:
        elapsed = monotonic() - started
        ui.register(None, "Invalid", elapsed, False)
        ui.progress(state.assessed, state.assessed, elapsed)
        return None

    valid = validate(term)
    if valid and not state.minimize:
        elapsed = monotonic() - started
        ui.register(term, [], elapsed, True)
        ui.progress(state.assessed, state.assessed, elapsed)
        ind.valid = True
        ind.fitness = []
        return term

    score: list[float] | str = "Invalid"
    is_best = False
    if valid:
        try:
            values = evaluate(term)
        except (InvalidIndividualException, TimeoutInEvaluationException):
            pass
        else:
            if len(values) != len(state.minimize):
                raise ValueError(f"Expected {len(state.minimize)} objective values, got {len(values)}")
            ind.valid = True
            ind.fitness = values
            state.pareto_front, is_best = update_pareto_front(state.pareto_front, values, term, state.minimize)
            score = values

    elapsed = monotonic() - started
    ui.register(term, score, elapsed, is_best)
    ui.progress(state.assessed, state.assessed, elapsed)
    return None


def _resample_generation_params(state: GPState, pop_size: int) -> None:
    state.tournament_size = state.rng.randint(2, max(2, pop_size))
    state.mutation_codons = state.rng.randint(1, 8)
    state.novelty_rate = state.rng.random() * 0.2  # up to 20% random immigrants


class GeneticProgrammingSynthesizer(Synthesizer):
    """Linear-genome genetic programming with adaptive population sizing."""

    def __init__(self, seed: int = 0):
        self.seed = seed

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
        assert isinstance(ctx, TypingContext)
        assert isinstance(type, Type)

        goals: list[Goal] = metadata.get(fun_name, {}).get("goals", [])
        minimize = [goal.minimize for goal in goals for _ in range(goal.length)]
        rng = random.Random(self.seed)
        initial = initial_partial(ctx, type)
        skip = make_skip(fun_name, metadata)
        started = monotonic()

        state = GPState(
            rng=rng,
            minimize=minimize,
            crossover_rate=rng.random(),
            mutation_rate=rng.random(),
        )
        _resample_generation_params(state, MIN_POPULATION)

        def fresh_individual(length: int | None = None) -> Individual:
            glen = length if length is not None else rng.randint(4, 24 + 4 * state.generation)
            return Individual(genome=_random_genome(rng, glen))

        # --- Timing probe: first 10 random individuals ---
        probe: list[Individual] = [fresh_individual() for _ in range(PROBE_INDIVIDUALS)]
        probe_started = monotonic()
        for ind in probe:
            early = _assess(ind, initial, skip, validate, evaluate, state, ui, started, budget)
            if early is not None:
                return early
            if monotonic() - started >= max(0.0, budget):
                break
        probe_seconds = monotonic() - probe_started

        pop_size = choose_population_size(probe_seconds, budget)
        population = list(probe)

        # Fill up to pop_size within remaining init allowance / overall budget.
        while len(population) < pop_size and monotonic() - started < max(0.0, budget):
            ind = fresh_individual()
            early = _assess(ind, initial, skip, validate, evaluate, state, ui, started, budget)
            if early is not None:
                return early
            population.append(ind)

        pop_size = len(population)
        if pop_size == 0:
            return None

        # --- Generational loop ---
        while monotonic() - started < max(0.0, budget):
            state.generation += 1
            _resample_generation_params(state, pop_size)
            # Allow longer genomes (deeper trees) as evolution advances.
            elite_n = min(_elite_count(pop_size), pop_size)
            ranked = sorted(population, key=lambda ind: _fitness_key(ind.fitness, minimize))
            next_pop: list[Individual] = [
                Individual(genome=list(ind.genome), term=ind.term, fitness=ind.fitness, valid=ind.valid)
                for ind in ranked[:elite_n]
            ]

            while len(next_pop) < pop_size:
                if monotonic() - started >= max(0.0, budget):
                    break

                if state.rng.random() < state.novelty_rate:
                    child = fresh_individual()
                elif state.rng.random() < state.crossover_rate and pop_size >= 2:
                    p1 = tournament_select(state.rng, population, state.tournament_size, minimize)
                    p2 = tournament_select(state.rng, population, state.tournament_size, minimize)
                    g1, g2 = one_point_crossover(state.rng, p1.genome, p2.genome)
                    if state.rng.random() < state.mutation_rate:
                        g1 = mutate(state.rng, g1, state.mutation_rate, state.mutation_codons)
                    child = Individual(genome=g1)
                    # Second offspring if room.
                    if len(next_pop) + 1 < pop_size:
                        if state.rng.random() < state.mutation_rate:
                            g2 = mutate(state.rng, g2, state.mutation_rate, state.mutation_codons)
                        sibling = Individual(genome=g2)
                        early = _assess(sibling, initial, skip, validate, evaluate, state, ui, started, budget)
                        if early is not None:
                            return early
                        next_pop.append(sibling)
                        if len(next_pop) >= pop_size:
                            break
                else:
                    parent = tournament_select(state.rng, population, state.tournament_size, minimize)
                    genome = mutate(state.rng, parent.genome, max(state.mutation_rate, 0.05), state.mutation_codons)
                    child = Individual(genome=genome)

                early = _assess(child, initial, skip, validate, evaluate, state, ui, started, budget)
                if early is not None:
                    return early
                next_pop.append(child)

            if len(next_pop) < elite_n:
                break
            population = next_pop[:pop_size]

        if not state.minimize:
            # No objectives and nothing validated during search.
            return None
        if not state.pareto_front:
            return None
        return random.Random(self.seed).choice(state.pareto_front)[1]
