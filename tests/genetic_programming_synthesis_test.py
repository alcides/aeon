"""Semantics specific to native genetic-programming synthesis."""

import random

from aeon.core.terms import Literal
from aeon.core.types import t_int
from aeon.synthesis.decorators import Goal
from aeon.synthesis.modules import genetic_programming as gp
from aeon.synthesis.modules.genetic_programming import (
    GeneticProgrammingSynthesizer,
    choose_population_size,
    map_genome,
    mutate,
    one_point_crossover,
)
from aeon.synthesis.modules.native_search import initial_partial
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.synthesis.modules.tdsyn.worklist import PartialAST
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def test_factory_uses_native_gp():
    assert isinstance(make_synthesizer("gp"), GeneticProgrammingSynthesizer)


def test_population_size_fits_init_budget_fraction():
    # 10 individuals took 1.0s; 10% of 100s budget is 10s → room for ~100 total.
    assert choose_population_size(probe_seconds=1.0, budget=100.0, probe_n=10) == 100
    # Probe already ate the whole 10% allowance → keep the probe size.
    assert choose_population_size(probe_seconds=5.0, budget=10.0, probe_n=10) == 10
    # Tiny budget still yields a minimal population.
    assert choose_population_size(probe_seconds=0.01, budget=0.05, probe_n=10) >= 2


def test_map_genome_produces_term_from_codons(monkeypatch):
    ctx = TypingContext()
    initial = initial_partial(ctx, t_int)
    closed = [
        PartialAST(Literal(0, t_int), [], 1),
        PartialAST(Literal(1, t_int), [], 1),
        PartialAST(Literal(2, t_int), [], 1),
    ]
    monkeypatch.setattr(gp, "literal_completions", lambda _p: [])
    monkeypatch.setattr(gp, "expansions_for_hole", lambda *_a, **_k: closed)
    term = map_genome([5], initial, lambda _n: False, generation=0)
    assert term == Literal(2, t_int)  # 5 % 3 == 2


def test_crossover_and_mutation_preserve_or_grow_genome():
    rng = random.Random(0)
    a = [1, 2, 3, 4, 5]
    b = [9, 8, 7]
    c1, c2 = one_point_crossover(rng, a, b)
    assert len(c1) + len(c2) == len(a) + len(b)
    grown = mutate(rng, a, mutation_rate=1.0, mutation_codons=3)
    assert grown  # non-empty


def test_without_objectives_returns_first_valid(monkeypatch):
    terms = [Literal(0, t_int), Literal(1, t_int), Literal(2, t_int)]
    calls = {"n": 0}

    def fake_map(genome, initial, skip, generation=0):
        i = min(calls["n"], len(terms) - 1)
        calls["n"] += 1
        return terms[i]

    monkeypatch.setattr(gp, "map_genome", fake_map)
    validated = []

    def validate(candidate):
        validated.append(candidate)
        return candidate.value == 1

    def must_not_evaluate(_c):
        raise AssertionError("no evaluate without objectives")

    result = GeneticProgrammingSynthesizer(seed=0).synthesize(
        TypingContext(),
        t_int,
        validate,
        must_not_evaluate,
        Name("f", 0),
        {},
        budget=100,
        ui=SilentSynthesisUI(),
    )
    assert result == Literal(1, t_int)
    assert Literal(1, t_int) in validated


def test_with_objectives_keeps_pareto_and_picks_with_seed(monkeypatch):
    terms = [Literal(i, t_int) for i in range(12)]
    idx = {"n": 0}

    def fake_map(genome, initial, skip, generation=0):
        i = idx["n"] % len(terms)
        idx["n"] += 1
        return terms[i]

    monkeypatch.setattr(gp, "map_genome", fake_map)

    # Stay under budget for the first ~30 clock reads (probe + a bit of evolution),
    # then jump past the budget so the loop exits and Pareto selection runs.
    clock = {"n": 0}

    def fake_monotonic():
        clock["n"] += 1
        return 100.0 if clock["n"] > 30 else 0.01 * clock["n"]

    monkeypatch.setattr(gp, "monotonic", fake_monotonic)

    function = Name("f", 0)
    metadata = {function: {"goals": [Goal(minimize=True, length=1, function=Name("min", 0))]}}
    chosen = []

    class _Rng(random.Random):
        def choice(self, seq):
            if seq and isinstance(seq[0], tuple) and len(seq[0]) == 2:
                chosen.append(seq)
                return seq[0]
            return super().choice(seq)

    monkeypatch.setattr(gp.random, "Random", _Rng)

    result = GeneticProgrammingSynthesizer(seed=7).synthesize(
        TypingContext(),
        t_int,
        lambda _c: True,
        lambda candidate: [float(candidate.value)],
        function,
        metadata,
        budget=1.0,
        ui=SilentSynthesisUI(),
    )
    assert chosen
    assert result is not None
