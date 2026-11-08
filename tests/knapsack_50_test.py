"""The compact knapsack example selects a subset of 50 fixed items."""

from pathlib import Path

import pytest

from aeon.errors import LiquidTypeCheckingFailedRelation
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI

EXAMPLE = Path(__file__).resolve().parents[1] / "examples/synthesis/puzzle/knapsack_50.ae"
FITS = "fun w => fun rest => w + rest <= 100"
PACK_TYPE = f"Knapsack{{|{FITS}|}}"


def _driver(synthesizer="none", budget=0):
    return AeonDriver(AeonConfig(synthesizer, SilentSynthesisUI(), budget, strict_decidable=True))


def _pack(items, *, qualified=False):
    empty = f"Knapsack.empty{{|{FITS}|}}" if qualified else "empty"
    take = f"Knapsack.take{{|{FITS}|}}" if qualified else "take"
    result = empty
    for item in reversed(items):
        result = f"{take} {item} ({result})"
    return result


def test_all_50_items_are_available():
    source = EXAMPLE.read_text().split("@maximize", 1)[0]
    source += "\n".join(f"def item_{i}: {PACK_TYPE} := {_pack([i], qualified=True)};" for i in range(1, 51))
    source += "\ndef main (u: Int): Int := 0;"
    assert not _driver().parse(aeon_code=source)


@pytest.mark.parametrize("items", [[], [50], [50, 49, 1], [22, *range(12, 0, -1)]])
def test_feasible_packs_typecheck_and_have_the_expected_value(items):
    driver = _driver()
    assert not driver.parse(aeon_code=EXAMPLE.read_text().replace("?items", _pack(items)))
    assert driver.run() == sum(2 * item + 1 for item in items)


@pytest.mark.parametrize("items", [[0], [51], [50, 50], [1, 50], [50, 49, 2]])
def test_type_rejects_invalid_items_duplicates_and_excess_weight(items):
    errors = _driver().parse(aeon_code=EXAMPLE.read_text().replace("?items", _pack(items)))
    assert errors
    assert all(isinstance(error, LiquidTypeCheckingFailedRelation) for error in errors)


def test_synthesis_maximizes_value_within_the_refined_type():
    source = EXAMPLE.read_text().rsplit("def main", 1)[0]
    source += f"def main (u: Int): {PACK_TYPE} := solution;"
    driver = _driver("enumerative", budget=10)
    assert not driver.parse(aeon_code=source)
    assert driver.has_synth()
    driver.synth()
    pack = driver.run()
    items = []
    while pack[0] == "Knapsack_take":
        _, item, pack = pack
        items.append(item)
    assert pack == ("Knapsack_empty",)
    assert all(1 <= item <= 50 for item in items)
    assert items == sorted(set(items), reverse=True)
    assert sum(items) <= 100
    # The optimizer must improve on the always-feasible empty knapsack.
    assert sum(2 * item + 1 for item in items) > 0
