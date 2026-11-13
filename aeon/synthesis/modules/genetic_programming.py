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
from dataclasses import dataclass, field, replace
from time import monotonic

from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import InvalidIndividualException, TimeoutInEvaluationException
from aeon.synthesis.joint import HoleSpec, JointCandidate, JointSynthesizer
from aeon.synthesis.decorators import Goal
from aeon.synthesis.modules.native_search import (
    ParetoEntry,
    expansions_for_hole,
    initial_partial,
    literal_completions,
    make_skip,
)
from aeon.synthesis.modules.tdsyn.helpers import clear_tdsyn_caches
from aeon.synthesis.pareto import dominates, minimize_flags_from_goals, pick_pareto_member, update_pareto_front
from aeon.synthesis.modules.tdsyn.worklist import PartialAST
from aeon.synthesis.qtt import QTTValidator
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

    partial = replace(initial, holes=list(initial.holes))
    if not partial.qtt_feasible():
        return None
    gene_i = 0
    wraps = 0
    choices_used = 0
    choice_budget = BASE_CHOICE_BUDGET * (1 + generation)

    while not partial.is_complete():
        completions = [
            term for term in literal_completions(partial) if replace(partial, term=term, holes=[]).qtt_feasible()
        ]
        if completions:
            codon = genome[gene_i % len(genome)]
            gene_i += 1
            if gene_i >= len(genome) * (wraps + 1):
                wraps += 1
            return completions[codon % len(completions)]

        hole = partial.holes[0]
        options = [
            option
            for option in expansions_for_hole(partial, hole, skip, max_depth=None, prune=False)
            if option.qtt_feasible()
        ]
        if not options:
            return None

        force_terminal = choices_used >= choice_budget or wraps >= max(1, 1 + generation)
        if force_terminal:
            # Close this hole even when other argument holes remain. Requiring
            # the entire partial term to close prevents multi-argument trees
            # from terminating after the genome's growth budget is exhausted.
            closed = [opt for opt in options if len(opt.holes) < len(partial.holes)]
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

    return partial.term if partial.qtt_feasible() else None


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


def _pareto_ranks(population: list[Individual], minimize: list[bool]) -> list[int]:
    """Rank valid individuals by successive non-dominated fronts, best first.

    Equal fitness vectors retain separate population slots at the same rank.
    Invalid or unevaluated individuals rank below every valid front. Build the
    dominance graph once so peeling further fronts needs no more comparisons.
    """
    scored = [(i, ind.fitness) for i, ind in enumerate(population) if ind.valid and ind.fitness is not None]
    dominated: list[list[int]] = [[] for _ in population]
    dominators = [0] * len(population)
    for pos, (i, score) in enumerate(scored):
        for j, other in scored[pos + 1 :]:
            if dominates(score, other, minimize):
                dominated[i].append(j)
                dominators[j] += 1
            elif dominates(other, score, minimize):
                dominated[j].append(i)
                dominators[i] += 1

    ranks = [-1] * len(population)
    front = [i for i, _ in scored if dominators[i] == 0]
    rank = 0
    while front:
        next_front = []
        for i in front:
            ranks[i] = rank
            for j in dominated[i]:
                dominators[j] -= 1
                if dominators[j] == 0:
                    next_front.append(j)
        front = next_front
        rank += 1
    return [rank if value < 0 else value for value in ranks]


def tournament_select(
    rng: random.Random,
    population: list[Individual],
    k: int,
    minimize: list[bool],
    *,
    ranks: list[int] | None = None,
) -> Individual:
    """Prefer the best population Pareto rank, with seeded random ties.

    A generation can supply precomputed ranks for all its tournaments. With
    zero or one objective, retain the original scalar tournament behavior.
    """
    k = max(1, min(k, len(population)))
    if len(minimize) > 1:
        ranks = _pareto_ranks(population, minimize) if ranks is None else ranks
        indices = rng.sample(range(len(population)), k)
        best_rank = min(ranks[i] for i in indices)
        return population[rng.choice([i for i in indices if ranks[i] == best_rank])]
    contestants = rng.sample(population, k)
    return _best_individual(contestants, minimize)


def _fitness_key(fitness: list[float] | None, minimize: list[bool]) -> tuple:
    """Legacy scalar sort key, used only with zero or one objective."""
    if fitness is None:
        return (1, ())
    oriented = tuple(v if is_min else -v for v, is_min in zip(fitness, minimize))
    return (0, oriented)


def _best_individual(population: list[Individual], minimize: list[bool]) -> Individual:
    valid = [ind for ind in population if ind.valid and ind.fitness is not None]
    pool = valid if valid else population
    return min(pool, key=lambda ind: _fitness_key(ind.fitness, minimize))


def select_elites(
    rng: random.Random,
    population: list[Individual],
    count: int,
    minimize: list[bool],
    *,
    ranks: list[int] | None = None,
) -> list[Individual]:
    """Keep the best fronts, randomly breaking ties at the elite cutoff."""
    count = max(0, min(count, len(population)))
    if len(minimize) <= 1:
        return sorted(population, key=lambda ind: _fitness_key(ind.fitness, minimize))[:count]
    ranks = _pareto_ranks(population, minimize) if ranks is None else ranks
    indices = list(range(len(population)))
    rng.shuffle(indices)
    indices.sort(key=lambda i: ranks[i])
    return [population[i] for i in indices[:count]]


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
    decode: Callable[[Genome, int], Term | None] | None = None,
) -> Term | None:
    """Map, validate and evaluate one individual. Return early term if no objectives."""
    term = (
        decode(ind.genome, state.generation)
        if decode is not None
        else map_genome(ind.genome, initial, skip, generation=state.generation)
    )
    ind.term = term
    ind.fitness = None
    ind.valid = False
    state.assessed += 1

    if term is None:
        elapsed = monotonic() - started
        ui.register(None, "Invalid", elapsed, False)
        ui.progress(state.assessed, state.assessed, elapsed)
        return None

    valid = (decode is not None or replace(initial, term=term, holes=[]).qtt_feasible()) and validate(term)
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
            if all(math.isfinite(value) for value in values):
                ind.valid = True
                ind.fitness = values
                state.pareto_front, is_best = update_pareto_front(state.pareto_front, values, term, state.minimize)
                score = values

    elapsed = monotonic() - started
    if is_best:
        ui.register_front(state.pareto_front, elapsed)
    ui.register(term, score, elapsed, is_best)
    ui.progress(state.assessed, state.assessed, elapsed)
    return None


def _resample_generation_params(state: GPState, pop_size: int) -> None:
    state.tournament_size = state.rng.randint(2, max(2, pop_size))
    state.mutation_codons = state.rng.randint(1, 8)
    state.novelty_rate = state.rng.random() * 0.2  # up to 20% random immigrants


class GeneticProgrammingSynthesizer(JointSynthesizer):
    """Linear-genome genetic programming with adaptive population sizing."""

    supports_size_objective = True

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

        initial = replace(
            initial_partial(ctx, type),
            expected_type=type,
            context=ctx,
            check_sketch=validate.feasible if isinstance(validate, QTTValidator) else None,
        )
        return self._search(
            initial,
            make_skip(fun_name, metadata),
            validate,
            evaluate,
            fun_name,
            metadata,
            budget,
            ui,
        )

    def synthesize_joint(
        self,
        holes: tuple[HoleSpec, ...],
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        fun_name: Name,
        metadata: Metadata,
        budget: float = 60,
        ui: SynthesisUI = SynthesisUI(),
    ) -> JointCandidate | None:
        initials = [replace(initial_partial(h.ctx, h.type), expected_type=h.type, context=h.ctx) for h in holes]
        skips = [make_skip(h.function, metadata) for h in holes]
        width = len(holes)

        def decode(genome: Genome, generation: int) -> Term | None:
            # Interleaved codon streams give each typed element its own genome.
            # Evolution acts on the complete product; fitness never scores an
            # isolated element or substitutes placeholder siblings.
            if len(genome) < width:
                return None
            terms = [initial.term for initial in initials]
            for i, (initial, skip) in enumerate(zip(initials, skips)):
                if isinstance(validate, QTTValidator):
                    # Earlier elements are fixed; later ones remain holes. Every
                    # codon choice shares the surrounding sketch's QTT budget.
                    def check_sketch(candidate: Term) -> bool:
                        product = tuple(candidate if j == i else term for j, term in enumerate(terms))
                        return validate.feasible(JointCandidate(product))

                    initial = replace(initial, check_sketch=check_sketch)
                term = map_genome(genome[i::width], initial, skip, generation=generation)
                if term is None:
                    return None
                terms[i] = term
            return JointCandidate(tuple(terms))

        result = self._search(
            initials[0],
            skips[0],
            validate,
            evaluate,
            fun_name,
            metadata,
            budget,
            ui,
            decode=decode,
            min_genome_length=width,
        )
        assert result is None or isinstance(result, JointCandidate)
        return result

    def _search(
        self,
        initial: PartialAST,
        skip: Callable[[Name], bool],
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        fun_name: Name,
        metadata: Metadata,
        budget: float,
        ui: SynthesisUI,
        decode: Callable[[Genome, int], Term | None] | None = None,
        min_genome_length: int = 1,
        max_assessments: int | None = None,
        population_size: int | None = None,
    ) -> Term | None:
        clear_tdsyn_caches()
        goals: list[Goal] = metadata.get(fun_name, {}).get("goals", [])
        minimize = minimize_flags_from_goals(goals)
        rng = random.Random(self.seed)
        started = monotonic()

        state = GPState(
            rng=rng,
            minimize=minimize,
            crossover_rate=rng.random(),
            mutation_rate=rng.random(),
        )
        _resample_generation_params(state, MIN_POPULATION)

        def exhausted():
            return monotonic() - started >= max(0.0, budget) or (
                max_assessments is not None and state.assessed >= max_assessments
            )

        def fresh_individual(length: int | None = None) -> Individual:
            glen = (
                length
                if length is not None
                else rng.randint(max(4, min_genome_length), max(24 + 4 * state.generation, min_genome_length))
            )
            return Individual(genome=_random_genome(rng, glen))

        # --- Timing probe: first 10 random individuals ---
        probe: list[Individual] = [fresh_individual() for _ in range(PROBE_INDIVIDUALS)]
        probe_started = monotonic()
        for ind in probe:
            if max_assessments is not None and exhausted():
                break
            early = _assess(ind, initial, skip, validate, evaluate, state, ui, started, budget, decode)
            if early is not None:
                return early
            if exhausted():
                break
        probe_seconds = monotonic() - probe_started

        pop_size = population_size or choose_population_size(probe_seconds, budget)
        population = list(probe)

        # Fill up to pop_size within remaining init allowance / overall budget.
        while len(population) < pop_size and not exhausted():
            ind = fresh_individual()
            early = _assess(ind, initial, skip, validate, evaluate, state, ui, started, budget, decode)
            if early is not None:
                return early
            population.append(ind)

        pop_size = len(population)
        if pop_size == 0:
            return None

        # --- Generational loop ---
        while not exhausted():
            state.generation += 1
            _resample_generation_params(state, pop_size)
            # Allow longer genomes (deeper trees) as evolution advances.
            elite_n = min(_elite_count(pop_size), pop_size)
            # Parent selection and survival share one ranking of this generation.
            ranks = _pareto_ranks(population, minimize) if len(minimize) > 1 else None
            elites = select_elites(state.rng, population, elite_n, minimize, ranks=ranks)
            next_pop: list[Individual] = [
                Individual(genome=list(ind.genome), term=ind.term, fitness=ind.fitness, valid=ind.valid)
                for ind in elites
            ]

            while len(next_pop) < pop_size:
                if exhausted():
                    break

                if state.rng.random() < state.novelty_rate:
                    child = fresh_individual()
                elif state.rng.random() < state.crossover_rate and pop_size >= 2:
                    p1 = tournament_select(state.rng, population, state.tournament_size, minimize, ranks=ranks)
                    p2 = tournament_select(state.rng, population, state.tournament_size, minimize, ranks=ranks)
                    g1, g2 = one_point_crossover(state.rng, p1.genome, p2.genome)
                    if state.rng.random() < state.mutation_rate:
                        g1 = mutate(state.rng, g1, state.mutation_rate, state.mutation_codons)
                    child = Individual(genome=g1)
                    # Second offspring if room.
                    if len(next_pop) + 1 < pop_size:
                        if state.rng.random() < state.mutation_rate:
                            g2 = mutate(state.rng, g2, state.mutation_rate, state.mutation_codons)
                        sibling = Individual(genome=g2)
                        early = _assess(sibling, initial, skip, validate, evaluate, state, ui, started, budget, decode)
                        if early is not None:
                            return early
                        next_pop.append(sibling)
                        if len(next_pop) >= pop_size or (max_assessments is not None and exhausted()):
                            break
                else:
                    parent = tournament_select(state.rng, population, state.tournament_size, minimize, ranks=ranks)
                    genome = mutate(state.rng, parent.genome, max(state.mutation_rate, 0.05), state.mutation_codons)
                    child = Individual(genome=genome)

                early = _assess(child, initial, skip, validate, evaluate, state, ui, started, budget, decode)
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
        self.pareto_front = state.pareto_front
        ui.register_front(state.pareto_front, monotonic() - started)
        return pick_pareto_member(state.pareto_front, self.seed)
