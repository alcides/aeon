"""Knapsack decisions are synthesized under the relational weight constraint."""

from pathlib import Path
import random
import re
import sys

import pytest

from aeon.errors import LiquidTypeCheckingFailedRelation
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI

EXAMPLE = Path(__file__).resolve().parents[1] / "examples/synthesis/puzzle/knapsack_50.ae"
FITS = "fun w => fun previous => w + previous <= 100"
KNAPSACK = f"Knapsack{{|{FITS}|}}"


@pytest.fixture(autouse=True)
def recursion_limit():
    previous = sys.getrecursionlimit()
    sys.setrecursionlimit(max(previous, 10000))
    yield
    sys.setrecursionlimit(previous)


def _driver(synthesizer="none", budget=0):
    return AeonDriver(AeonConfig(synthesizer, SilentSynthesisUI(), budget, strict_decidable=True))


def _unpack(value):
    entries = []
    while value[0] == "Knapsack_add":
        _, previous, item_value, weight, used = value
        entries.append(((item_value, weight), used))
        value = previous
    assert value == ("Knapsack_empty",)
    # Each constructor appends a decision to the previous knapsack.
    return entries[::-1]


def _items():
    return [(int(value), int(weight)) for value, weight in re.findall(r"add k (\d+) (\d+) \?b\d+", EXAMPLE.read_text())]


def _program(items, decisions, size=None):
    source = EXAMPLE.read_text().split("@maximize", 1)[0]
    source += f"""
        def main (u:Int): {{k:{KNAPSACK} | Knapsack.size k = {len(items) if size is None else size} && Knapsack.weight k <= 100}} :=
            let add := Knapsack.add{{|{FITS}|}} in
            let k := Knapsack.empty{{|{FITS}|}} in
    """
    for (value, weight), used in zip(items, decisions):
        source += f"let k := add k {value} {weight} {str(used).lower()} in\n"
    return source + "k;"


def test_dataset_contains_50_reproducible_random_pairs():
    rng = random.Random(20261108)
    assert _items() == [(rng.randint(1, 100), rng.randint(1, 20)) for _ in range(50)]


@pytest.mark.parametrize("decisions", [[False, False, False], [True, True, False], [False, True, True]])
def test_feasible_decisions_are_returned_unchanged(decisions):
    items = [(7, 60), (100, 30), (8, 50)]
    driver = _driver()
    assert not driver.parse(aeon_code=_program(items, decisions))
    assert _unpack(driver.run()) == list(zip(items, decisions))


def test_exact_capacity_is_accepted():
    items, decisions = [(7, 60), (8, 40)], [True, True]
    driver = _driver()
    assert not driver.parse(aeon_code=_program(items, decisions))
    assert _unpack(driver.run()) == list(zip(items, decisions))


@pytest.mark.parametrize("items", [[(7, 101)], [(7, 60), (8, 50)]])
def test_overweight_decisions_are_rejected_instead_of_repaired(items):
    errors = _driver().parse(aeon_code=_program(items, [True] * len(items)))
    assert errors
    assert all(isinstance(error, LiquidTypeCheckingFailedRelation) for error in errors)


def test_length_refinement_rejects_a_missing_decision():
    assert _driver().parse(aeon_code=_program([(7, 60), (100, 30)], [True, False], size=3))


def test_synthesis_returns_the_50_decisions_with_optimal_value(monkeypatch):
    pytest.importorskip("ortools")
    from aeon.synthesis.modules.ortools_cpsat import CPSatHoleSynthesizer

    def no_runtime_fallback(*args, **kwargs):
        pytest.fail("the relational constraint must be enforced during symbolic optimization")

    monkeypatch.setattr(CPSatHoleSynthesizer, "_runtime_search", no_runtime_fallback)
    driver = _driver("ortools", budget=30)
    assert not driver.parse(aeon_code=EXAMPLE.read_text())
    assert driver.has_synth()
    driver.synth()
    entries = _unpack(driver.run())
    assert len(entries) == 50
    assert [item for item, _ in entries] == _items()
    assert all(type(used) is bool for _, used in entries)
    assert sum(weight for (_, weight), used in entries if used) <= 100
    value = sum(value for (value, _), used in entries if used)
    # Independent 0/1 dynamic program, with no Aeon evaluation or CP-SAT.
    best = [0] * 101
    for item_value, weight in _items():
        for capacity in range(100, weight - 1, -1):
            best[capacity] = max(best[capacity], best[capacity - weight] + item_value)
    assert value == best[100]
