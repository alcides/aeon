"""A Boolean-only knapsack mask carries its weight through logical measures."""

from pathlib import Path
import random
import sys

import pytest

from aeon.errors import LiquidTypeCheckingFailedRelation
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI

EXAMPLE = Path(__file__).resolve().parents[1] / "examples/synthesis/puzzle/knapsack_50.ae"
FITS = "fun w => fun rest => w + rest <= 100"
MASK = f"Mask{{|{FITS}|}}"


@pytest.fixture(autouse=True)
def recursion_limit():
    previous = sys.getrecursionlimit()
    sys.setrecursionlimit(max(previous, 10000))
    yield
    sys.setrecursionlimit(previous)


def _driver(synthesizer="none", budget=0):
    return AeonDriver(AeonConfig(synthesizer, SilentSynthesisUI(), budget, strict_decidable=True))


def _unpack(value):
    decisions = []
    while value[0] == "Mask_cons":
        # Only a tail and a Boolean: no item data or cached weight in a node.
        _, value, used = value
        assert type(used) is bool
        decisions.append(used)
    assert value == ("Mask_empty",)
    return decisions


def _items():
    rng = random.Random(20261108)
    return [(rng.randint(1, 100), rng.randint(1, 20)) for _ in range(50)]


def _program(decisions, count=None, weight=None):
    source = EXAMPLE.read_text()
    # Keep the real import and datatype, without the unrelated objective/data list.
    source = (
        source[: source.index("inductive Item")]
        + "inductive Mask"
        + source.split("inductive Mask", 1)[1].split("def total_value", 1)[0]
    )
    exact_weight = "" if weight is None else f" && Mask.weight m = {weight}"
    source += f"""
        def main (u:Int): {{m:{MASK} | Mask.count m = {len(decisions) if count is None else count}
            && Mask.weight m <= 100{exact_weight}}} :=
            let cons := Mask.cons{{|{FITS}|}} in
            let mask := Mask.empty{{|{FITS}|}} in
    """
    for used in reversed(decisions):
        source += f"let mask := cons mask {str(used).lower()} in\n"
    return source + "mask;"


def test_dataset_contains_50_reproducible_random_pairs():
    source = EXAMPLE.read_text().split("inductive Mask", 1)[0]
    driver = _driver()
    assert not driver.parse(aeon_code=source + "def main (u:Int):List := items;")
    value = driver.run()
    pairs = []
    while value[0] == "List_cons":
        _, item, value = value
        assert item[0] == "Item_pair"
        pairs.append(item[1:])
    assert value == ("List_nil",)
    assert pairs == _items()


@pytest.mark.parametrize("decisions", [[], [True], [True, False], [True, False, False], [True] * 3, [False] * 3])
def test_boolean_nodes_preserve_decisions_and_prove_their_weight(decisions):
    # A partial mask is a suffix of the full 50-item mask.
    items = _items()[50 - len(decisions) :]
    weight = sum(weight for (_, weight), used in zip(items, decisions) if used)
    driver = _driver()
    assert not driver.parse(aeon_code=_program(decisions, weight=weight))
    assert _unpack(driver.run()) == decisions


def test_exact_capacity_is_accepted():
    selected = {4, 6, 9, 11, 16, 19, 25, 27, 31, 32, 34, 40, 41, 42, 45, 46}
    decisions = [i in selected for i in range(50)]
    assert sum(weight for (_, weight), used in zip(_items(), decisions) if used) == 100
    driver = _driver()
    assert not driver.parse(aeon_code=_program(decisions, weight=100))
    assert _unpack(driver.run()) == decisions


def test_overweight_decisions_are_rejected():
    decisions = [True] * 11
    assert sum(weight for _, weight in _items()[-11:]) > 100
    errors = _driver().parse(aeon_code=_program(decisions))
    assert errors
    assert all(isinstance(error, LiquidTypeCheckingFailedRelation) for error in errors)


def test_logical_weight_cannot_be_forged():
    # The first of the last three items weighs 9, not 10.
    assert _driver().parse(aeon_code=_program([True, False, False], weight=10))


def test_count_refinement_rejects_a_missing_decision():
    assert _driver().parse(aeon_code=_program([True, False], count=3))


def test_synthesis_returns_50_boolean_nodes_with_optimal_value(monkeypatch):
    pytest.importorskip("ortools")
    from aeon.synthesis.modules.ortools_cpsat import CPSatHoleSynthesizer

    def no_runtime_fallback(*args, **kwargs):
        pytest.fail("the relational constraint must be enforced during symbolic optimization")

    monkeypatch.setattr(CPSatHoleSynthesizer, "_runtime_search", no_runtime_fallback)
    driver = _driver("ortools", budget=30)
    assert not driver.parse(filename=str(EXAMPLE))
    assert driver.has_synth()
    driver.synth()
    decisions = _unpack(driver.run())
    assert len(decisions) == 50
    entries = list(zip(_items(), decisions))
    assert sum(weight for (_, weight), used in entries if used) <= 100
    value = sum(value for (value, _), used in entries if used)
    # Independent 0/1 dynamic program, with no Aeon evaluation or CP-SAT.
    best = [0] * 101
    for item_value, weight in _items():
        for capacity in range(100, weight - 1, -1):
            best[capacity] = max(best[capacity], best[capacity - weight] + item_value)
    assert value == best[100]
