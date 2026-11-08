"""The knapsack GA constructs only genomes whose total weight is at most 10."""

from __future__ import annotations

from pathlib import Path
from itertools import product

import pytest

from aeon.errors import CoreSubtypingError, LiquidTypeCheckingFailedRelation
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI

ROOT = Path(__file__).resolve().parents[1]
EXAMPLE = ROOT / "examples" / "knapsack_ga.ae"
WEIGHTS = (2, 3, 4, 5, 9)
VALUES = (3, 4, 5, 8, 10)
FITS = "fun selected => fun tail => selected + tail <= 10"


def _genome(bits, *, weights=WEIGHTS, values=VALUES, relation=FITS):
    result = f"Genome.empty_genome{{|{relation}|}}"
    for bit, weight, value in reversed(list(zip(bits, weights, values, strict=True))):
        result = f"Genome.gene{{|{relation}|}} {bit} {weight} {value} ({result})"
    return result


def _declarations():
    source = EXAMPLE.read_text().split("inductive Population", 1)[0]
    return source.replace("open List\n", "").replace("open Pair\n", "")


def _program(main, *, llvm=True):
    source = EXAMPLE.read_text().rsplit("def main", 1)[0] + main
    return source if llvm else source.replace("@llvm\n", "")


def _driver(*, no_main: bool = False) -> AeonDriver:
    return AeonDriver(
        AeonConfig(
            synthesizer="none",
            synthesis_ui=SilentSynthesisUI(),
            synthesis_budget=0,
            no_main=no_main,
            strict_decidable=True,
        )
    )


def test_fold_n_int_llvm():
    cfg = AeonConfig(synthesizer="none", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    driver = AeonDriver(cfg)
    source = """
open LoopKernels
@llvm
def add_i (acc: Int) (i: Int) : Int := acc + i;
@llvm
def sum_range (n: Int) : Int := fold_n_int add_i 0 n;
def main (x: Int) : Int := sum_range 10;
"""
    assert not driver.parse(aeon_code=source)
    assert driver.run() == 45


def test_knapsack_ga_example_typechecks():
    driver = _driver()
    assert not driver.parse(filename=str(EXAMPLE))


def test_knapsack_ga_example_runs(capsys):
    driver = _driver()
    assert not driver.parse(filename=str(EXAMPLE))
    result = driver.run()
    optimum = max(
        sum(bit * value for bit, value in zip(bits, VALUES, strict=True))
        for bits in product((0, 1), repeat=5)
        if sum(bit * weight for bit, weight in zip(bits, WEIGHTS, strict=True)) <= 10
    )
    assert isinstance(result, int)
    fitness = int(capsys.readouterr().out.strip().splitlines()[-1])
    assert 0 < fitness <= optimum == 15


@pytest.mark.parametrize("bits", list(product((0, 1), repeat=5)))
def test_individual_type_accepts_exactly_the_feasible_subsets(bits):
    source = _declarations() + f"def candidate: Individual := .individual ({_genome(bits)});"
    errors = _driver(no_main=True).parse(aeon_code=source)
    weight = sum(bit * weight for bit, weight in zip(bits, WEIGHTS, strict=True))
    if weight <= 10:
        assert not errors
    else:
        assert errors
        assert all(isinstance(error, LiquidTypeCheckingFailedRelation) for error in errors)


def test_individual_cannot_wrap_an_unconstrained_genome():
    unconstrained = _genome((1, 1, 1, 1, 1), relation="fun selected => fun tail => true")
    source = (
        _declarations()
        + f"""
def unconstrained: Genome{{|fun selected => fun tail => true|}} := {unconstrained};
def candidate: Individual := .individual unconstrained;
"""
    )
    errors = _driver(no_main=True).parse(aeon_code=source)
    assert errors
    assert all(isinstance(error, (CoreSubtypingError, LiquidTypeCheckingFailedRelation)) for error in errors)


@pytest.mark.parametrize("llvm", [False, True], ids=["interpreter", "llvm"])
@pytest.mark.parametrize(
    "bit,weight,tail_bit,tail_weight,expected", [(1, 2, 1, 8, 10), (1, 3, 1, 8, 8), (1, 11, 0, 0, 0)]
)
def test_prepend_preserves_capacity(llvm, bit, weight, tail_bit, tail_weight, expected):
    tail = _genome((tail_bit,), weights=(tail_weight,), values=(0,))
    source = _program(
        f"""
@llvm
def check (u: Int): Int :=
    let genes: Genome{{|{FITS}|}} := prepend_gene {bit} {weight} 0 ({tail}) in
    individual_weight (.individual genes)
def main (u: Int): Int := check u;
""",
        llvm=llvm,
    )
    driver = _driver()
    assert not driver.parse(aeon_code=source)
    assert driver.run() == expected


@pytest.mark.parametrize("llvm", [False, True], ids=["interpreter", "llvm"])
def test_crossover_and_mutation_repair_overweight_children(llvm):
    left = _genome((1, 1, 0, 0, 0))
    right = _genome((0, 0, 1, 1, 0))
    heavy = _genome((0, 0, 0, 0, 1))
    empty = _genome((0, 0, 0, 0, 0))
    # The existing LCG overflows LLVM's 32-bit Int, so its stream differs from
    # the interpreter's unbounded integers. Each seed flips just the first bit.
    mutation_seed = 32937 if llvm else 11004
    # The crossover seed makes no mutations. For the mutation cases,
    # adding weight 2 must be rejected for a weight-9 parent, and kept for an
    # empty parent. Encode both weight and fitness to observe the final child.
    source = _program(
        f"""
@llvm
def child_score (a: Individual) (b: Individual) (cut: Int) (seed: Int): Int :=
    let result: (Pair Int Individual) := crossover_mutate a b cut 0 seed in
    match result with
    | mk rng child => individual_weight child * 100 + evaluate_individual child
@llvm
def check (u: Int): Bool :=
    let a: Individual := .individual ({left}) in
    let b: Individual := .individual ({right}) in
    let h: Individual := .individual ({heavy}) in
    let e: Individual := .individual ({empty}) in
    child_score a b 2 20260913 = 913 &&
    child_score h h 2 {mutation_seed} = 910 &&
    child_score e e 2 {mutation_seed} = 203
def main (u: Int): Bool := check u;
""",
        llvm=llvm,
    )
    driver = _driver()
    assert not driver.parse(aeon_code=source)
    assert driver.run() is True


def test_creation_and_generations_preserve_items_and_capacity():
    # Return interpreter values so Python can independently sum the selected
    # item weights and check that repair never drops or alters an item.
    source = _program(
        """
def append_population (a: Population) (b: Population): Population :=
    match a with
    | empty_pop => b
    | member hd tl => .member hd (append_population tl b)

def history (n: Int) (rng: Int) (pop: Population): Population :=
    if n <= 0 then pop else
        let step: (Pair Int Population) := next_generation 5 10 pop rng in
        match step with
        | mk rng2 kids => append_population pop (history (n - 1) rng2 kids)

def main (u: Int): Population :=
    let started: (Pair Int Population) := init_population (puzzle_items 0) 10 20260913 in
    match started with
    | mk rng pop => history 10 rng pop;
""",
        llvm=False,
    )
    driver = _driver()
    assert not driver.parse(aeon_code=source)
    population = driver.run()
    individuals = []
    while population[0] == "Population_member":
        _, individual, population = population
        assert individual[0] == "Individual_individual"
        genes = individual[1]
        bits, weights, values = [], [], []
        while genes[0] == "Genome_gene":
            _, bit, weight, value, genes = genes
            bits.append(bit)
            weights.append(weight)
            values.append(value)
        assert genes == ("Genome_empty_genome",)
        assert tuple(weights) == WEIGHTS
        assert tuple(values) == VALUES
        assert set(bits) <= {0, 1}
        assert sum(bit * weight for bit, weight in zip(bits, weights, strict=True)) <= 10
        individuals.append(tuple(bits))
    assert population == ("Population_empty_pop",)
    assert len(individuals) == 110
    assert len(set(individuals)) > 1
