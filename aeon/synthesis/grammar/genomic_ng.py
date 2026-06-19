"""GenomicNG: Nevergrad-driven grammatical-evolution synthesis backend.

The search space is a fixed-length integer *genome* (a codon list, exactly the
representation geneticengine's :class:`GrammaticalEvolutionRepresentation`
already uses). Nevergrad treats it as a bounded integer vector and optimises it
with any of its derivative-free algorithms (NGOpt, CMA, DE, PSO, ...). Each
genome is decoded into an Aeon ``Term`` by the *existing* grammatical-evolution
mapper, and scored by the *existing* :func:`create_problem` fitness (the SMT
``validate`` predicate plus any ``@minimize``/``@maximize`` objectives).

This means GenomicNG reuses Aeon's whole synthesis stack — grammar generation,
phenotype decoding, fitness — and only swaps the *search strategy* for
Nevergrad's. The single design choice is the genome↔derivation encoding, and we
borrow geneticengine's codon mapping rather than inventing our own.
"""

from __future__ import annotations

import time
from typing import Any, Callable

from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer
from aeon.synthesis.grammar.ge_synthesis import create_problem
from aeon.synthesis.grammar.grammar_generation import create_grammar
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name

from geneticengine.problems import Fitness, Problem
from geneticengine.random.sources import NativeRandomSource
from geneticengine.representations.grammatical_evolution.ge import (
    Genotype,
    GrammaticalEvolutionRepresentation,
)
from geneticengine.representations.tree.initializations import MaxDepthDecider

# Upper bound on a codon. The decoder reduces each codon modulo the local choice
# arity, so the exact ceiling only sets resolution: large enough that
# ``codon % small_arity`` is close to uniform, small enough that Nevergrad's
# continuous relaxation explores it well.
CODON_MAX = 1 << 15
GENE_LENGTH = 256
MAX_DEPTH = 5

# Finite penalty reported to Nevergrad for an invalid/un-evaluable candidate.
# A large positive value keeps such candidates strictly worse than any real
# (minimisation-oriented) loss without tripping Nevergrad's inf-clipping warning.
INVALID_PENALTY = 1e12


def _orient(components: list[float], minimize: list[bool]) -> list[float]:
    """Re-orient a fitness vector so every objective is minimised.

    Nevergrad always minimises; geneticengine records per-objective direction in
    ``problem.minimize``. Maximise objectives are negated.
    """
    return [c if mini else -c for c, mini in zip(components, minimize)]


def _knee_point(archive: list[tuple[Term, list[float]]], minimize: list[bool]) -> Term | None:
    """Compromise selection over an archive of (term, oriented-loss) pairs.

    Mirrors ``ge_synthesis._knee_point_individual``: per-objective min-max
    normalisation, then the candidate closest to the utopia origin. Works for
    the single-objective case too (one dimension → picks the lowest loss).
    """
    if not archive:
        return None
    if len(archive) == 1:
        return archive[0][0]

    n_obj = len(minimize)
    losses = [loss for _, loss in archive]
    mins = [min(l[d] for l in losses) for d in range(n_obj)]
    maxs = [max(l[d] for l in losses) for d in range(n_obj)]
    spreads = [maxs[d] - mins[d] for d in range(n_obj)]

    def dist2(loss: list[float]) -> float:
        total = 0.0
        for d in range(n_obj):
            if spreads[d] > 0:
                norm = (loss[d] - mins[d]) / spreads[d]
                total += norm * norm
        return total

    best = min(archive, key=lambda pair: dist2(pair[1]))
    return best[0]


class GenomicNGSynthesizer(Synthesizer):
    """Synthesis by optimising a codon genome with Nevergrad.

    Args:
        optimizer: name of a Nevergrad optimiser class (e.g. ``"NGOpt"``,
            ``"CMA"``, ``"DE"``, ``"PSO"``, ``"TBPSA"``).
        seed: seed for both the Nevergrad optimiser and the codon decoder.
        gene_length: number of codons in the genome.
    """

    def __init__(self, optimizer: str = "NGOpt", seed: int = 0, gene_length: int = GENE_LENGTH):
        self.optimizer = optimizer
        self.seed = seed
        self.gene_length = gene_length

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
        output_value: Callable[[Term], Any] | None = None,
    ) -> Term:
        assert isinstance(ctx, TypingContext)
        assert isinstance(type, Type)

        try:
            import nevergrad as ng
        except ImportError as e:  # pragma: no cover - optional dependency
            raise ImportError(
                "GenomicNG requires the 'nevergrad' package. Install it with "
                "`uv pip install nevergrad` (or the 'synthesis-ng' extra)."
            ) from e

        grammar = create_grammar(ctx, type, fun_name, metadata)
        problem: Problem = create_problem(validate, evaluate, fun_name, metadata)
        minimize = problem.minimize

        representation = GrammaticalEvolutionRepresentation(
            grammar,
            decider=MaxDepthDecider(NativeRandomSource(self.seed), grammar, max_depth=MAX_DEPTH),
            gene_length=self.gene_length,
        )

        # The genome: a fixed-length integer codon vector. Nevergrad mutates the
        # continuous relaxation; integer casting + modulo decoding turn it back
        # into a derivation.
        parametrization = ng.p.Array(shape=(self.gene_length,)).set_bounds(0, CODON_MAX).set_integer_casting()
        parametrization.random_state.seed(self.seed)

        opt_cls = ng.optimizers.registry[self.optimizer]
        # A generous evaluation cap; the real stop is the wall-clock budget below.
        optimizer = opt_cls(parametrization=parametrization, budget=10**9, num_workers=1)

        archive: list[tuple[Term, list[float]]] = []
        best_term: Term | None = None
        best_fitness: Fitness | None = None
        start = time.monotonic()

        while time.monotonic() - start < budget:
            candidate = optimizer.ask()
            dna = [int(x) for x in candidate.value]
            phenotype = representation.genotype_to_phenotype(Genotype(dna))
            core = phenotype.get_core()
            assert isinstance(core, Term)

            try:
                fitness = problem.evaluate(phenotype)
                oriented = _orient(fitness.fitness_components, minimize)
                valid = fitness.valid
            except Exception:
                # A black-box search constantly proposes candidates the decoder
                # turns into ill-typed or un-evaluable terms (e.g. validate/SMT
                # throws). Treat any evaluation failure as an invalid candidate
                # and penalise it rather than aborting the whole search.
                fitness = problem.get_invalid_fitness()
                oriented = [INVALID_PENALTY] * len(minimize)
                valid = False

            loss = oriented if len(oriented) > 1 else oriented[0]
            optimizer.tell(candidate, loss)

            ui.register(core, fitness, time.monotonic() - start, is_best=False)

            if valid:
                archive.append((core, oriented))
                if best_fitness is None or problem.is_better(fitness, best_fitness):
                    best_term, best_fitness = core, fitness
                # Stop as soon as the goal is met (e.g. a validate-only target,
                # or all objectives at/under their targets) instead of burning
                # the rest of the time budget.
                if problem.is_solved(fitness):
                    break

        # Single objective: ``best_term`` is already the optimum. Multi
        # objective: ``is_better`` is only a partial order, so resolve the
        # Pareto archive by knee-point compromise.
        if len(minimize) > 1:
            chosen = _knee_point(archive, minimize)
            return chosen if chosen is not None else best_term
        return best_term
