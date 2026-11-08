"""The knapsack selects from 50 fixed pairs with a positional Boolean mask."""

from pathlib import Path
import random
import re
import sys

import pytest

from aeon.errors import LiquidTypeCheckingFailedRelation
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI

EXAMPLE = Path(__file__).resolve().parents[1] / "examples/synthesis/puzzle/knapsack_50.ae"
FITS = "fun w => fun rest => w + rest <= 100"
SELECTION = f"Selection{{|{FITS}|}}"


@pytest.fixture(autouse=True)
def recursion_limit():
    # Match the CLI limit when compiling the two 50-element list literals.
    previous = sys.getrecursionlimit()
    sys.setrecursionlimit(max(previous, 10000))
    yield
    sys.setrecursionlimit(previous)


def _driver(synthesizer="none", budget=0):
    return AeonDriver(AeonConfig(synthesizer, SilentSynthesisUI(), budget, strict_decidable=True))


def _helpers():
    source = EXAMPLE.read_text()
    return (
        source.split("def items:", 1)[0]
        + "inductive Selection"
        + source.split("inductive Selection", 1)[1].split("@maximize", 1)[0]
    )


def _unpack_list(value):
    result = []
    while value[0] == "List_cons":
        _, head, value = value
        result.append(head)
    assert value == ("List_nil",)
    return result


def _items():
    literal = EXAMPLE.read_text().split("def items:", 1)[1].split("];", 1)[0]
    return [(int(value), int(weight)) for value, weight in re.findall(r"pair (\d+) (\d+)", literal)]


def test_dataset_contains_50_reproducible_random_pairs():
    rng = random.Random(20261108)
    assert _items() == [(rng.randint(1, 100), rng.randint(1, 20)) for _ in range(50)]


@pytest.mark.parametrize(
    "mask, expected",
    [
        ("false, false, false", [False, False, False]),
        ("true, true, false", [True, True, False]),
        ("true, true, true", [False, True, True]),
    ],
)
def test_selection_preserves_positions_and_respects_capacity(mask, expected):
    driver = _driver()
    source = (
        _helpers()
        + f"""
        def main (u:Int): {{xs:(List Bool) | List.size xs = 3}} :=
            booleans (select [pair 7 60, pair 100 30, pair 8 50] [{mask}]);
    """
    )
    assert not driver.parse(aeon_code=source)
    assert _unpack_list(driver.run()) == expected


def test_relational_type_rejects_an_overweight_selection():
    source = (
        _helpers()
        + f"""
        def main (u:Int): {SELECTION} :=
            Selection.cons{{|{FITS}|}} true 60
                (Selection.cons{{|{FITS}|}} true 50 (Selection.empty{{|{FITS}|}}));
    """
    )
    errors = _driver().parse(aeon_code=source)
    assert errors
    assert all(isinstance(error, LiquidTypeCheckingFailedRelation) for error in errors)


def test_length_refinement_rejects_a_missing_decision():
    source = (
        _helpers()
        + """
        def main (u:Int): {xs:(List Bool) | List.size xs = 3} :=
            booleans (select [pair 7 60, pair 100 30] [true, false]);
    """
    )
    assert _driver().parse(aeon_code=source)


def test_synthesis_returns_50_booleans_with_optimal_value(monkeypatch):
    pytest.importorskip("ortools")
    from aeon.synthesis.modules.ortools_cpsat import CPSatHoleSynthesizer

    def no_runtime_fallback(*args, **kwargs):
        pytest.fail("the 50 Boolean decisions must be optimized symbolically")

    monkeypatch.setattr(CPSatHoleSynthesizer, "_runtime_search", no_runtime_fallback)
    driver = _driver("ortools", budget=30)
    assert not driver.parse(aeon_code=EXAMPLE.read_text())
    assert driver.has_synth()
    driver.synth()
    mask = _unpack_list(driver.run())
    assert len(mask) == 50
    assert all(type(used) is bool for used in mask)
    items = _items()
    assert sum(weight for (_, weight), used in zip(items, mask) if used) <= 100
    value = sum(value for (value, _), used in zip(items, mask) if used)
    # Independent 0/1 dynamic program, with no Aeon evaluation or CP-SAT.
    best = [0] * 101
    for item_value, weight in items:
        for capacity in range(100, weight - 1, -1):
            best[capacity] = max(best[capacity], best[capacity - weight] + item_value)
    assert value == best[100]
