"""Synthesize every Hakank instance and independently check its combinatorial goal."""

from __future__ import annotations

import json
from itertools import combinations, permutations, product
from pathlib import Path

import pytest

from aeon.backend.evaluator import eval as aeon_eval
from aeon.core.terms import Literal, Var
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.evaluation_pool import set_program_tail
from aeon.synthesis.identification import iterate_top_level
from aeon.synthesis.uis.api import SilentSynthesisUI
from scripts.generate_hakank_examples import models

ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / "examples/synthesis/hakank"
MANIFEST = json.loads((SUITE / "manifest.json").read_text())
ENTRIES = {entry["name"]: entry for entry in MANIFEST["models"]}


def test_generated_examples_match_their_documented_instances():
    assert len(ENTRIES) == 25
    assert {path.stem for path in SUITE.glob("*.ae")} == set(ENTRIES)
    for model in models():
        assert model.render(ENTRIES[model.name]) == (SUITE / f"{model.name}.ae").read_text()
        assert ENTRIES[model.name]["source_url"].startswith("https://github.com/hakank/hakank/blob/")


def check_assignment(name, values, data):
    """Use Python's sets, arithmetic, and indexing, independently of Aeon formulas."""
    x = [values[k] for k in values if k.startswith("x")]
    if name == "send_more_money":
        assert len(set(values.values())) == 8

        def number(letters):
            return int("".join(str(values[letter]) for letter in letters))

        assert number("send") + number("more") == number("money")
    elif name == "nqueens":
        q = list(values.values())
        assert len(set(q)) == 8
        assert len({i + v for i, v in enumerate(q)}) == 8
        assert len({i - v for i, v in enumerate(q)}) == 8
    elif name in ("sudoku", "quasigroup_completion"):
        n = data["size"]
        target = set(range(1, n + 1))
        for i in range(n):
            assert set(x[i * n : (i + 1) * n]) == target
            assert set(x[i::n]) == target
            for j in range(n):
                if data["clues"][i][j]:
                    assert x[i * n + j] == data["clues"][i][j]
        if name == "sudoku":
            for row, col in product((0, 2), repeat=2):
                assert {x[(row + i) * n + col + j] for i, j in product(range(2), repeat=2)} == target
    elif name == "magic_square":
        assert set(x) == set(range(1, 10))
        assert all(sum(x[i::3]) == sum(x[i * 3 : (i + 1) * 3]) == 15 for i in range(3))
        assert sum(x[::4]) == x[2] + x[4] + x[6] == 15
    elif name == "all_interval":
        assert set(x) == set(range(1, 6))
        assert {abs(a - b) for a, b in zip(x, x[1:])} == set(range(1, 5))
    elif name == "all_different_except_0":
        nonzero = [v for v in x if v]
        assert len(nonzero) == len(set(nonzero))
    elif name == "among":
        assert sum(v in {1, 5, 8} for v in x) == 3
    elif name in ("assignment", "ski_assignment"):
        rows, cols = len(data["cost"]), len(data["cost"][0])
        chosen = []
        for i in range(rows):
            row = x[i * cols : (i + 1) * cols]
            assert sum(row) == 1
            chosen.append(row.index(1))
        assert len(set(chosen)) == rows
        cost = sum(data["cost"][i][j] for i, j in enumerate(chosen))
        # Enumerate assignments, independent of the binary-matrix encoding.
        assert cost == min(sum(data["cost"][i][j] for i, j in enumerate(p)) for p in permutations(range(cols), rows))
    elif name == "set_covering":
        assert all(any(x[j] and distance <= 15 for j, distance in enumerate(row)) for row in data["distances"])
        assert sum(x) == 2
    elif name in ("subset_sum", "xkcd"):
        assert sum(w * v for w, v in zip(data["weights"], x)) == data["target"]
    elif name == "knapsack":
        assert sum(w * v for w, v in zip(data["weights"], x)) <= data["capacity"]
        benefit = sum(v * selected for v, selected in zip(data["values"], x))
        assert benefit == max(
            sum(v * s for v, s in zip(data["values"], bits))
            for bits in product((0, 1), repeat=len(x))
            if sum(w * s for w, s in zip(data["weights"], bits)) <= data["capacity"]
        )
    elif name == "bin_packing":
        assert all(
            sum(w for w, label in zip(data["weights"], x) if label == bin_id) <= data["capacity"] for bin_id in set(x)
        )
        assert len(set(x)) == 2
    elif name == "langford":
        p = list(values.values())
        assert set(p) == set(range(6))
        sequence = [0] * 6
        for i in range(3):
            sequence[p[i]] = sequence[p[i + 3]] = i + 1
        for value in range(1, 4):
            positions = [i for i, v in enumerate(sequence) if v == value]
            assert positions[1] - positions[0] == value + 1
    elif name == "map_coloring":
        assert all(x[i] != x[j] for i, j in data["edges"])
    elif name == "golomb_ruler":
        assert x == sorted(x) and len(set(x)) == 4 and x[0] == 0 and x[-1] == 6
        assert len({b - a for a, b in combinations(x, 2)}) == 6
    elif name == "magic_sequence":
        assert all(x.count(i) == x[i] for i in range(len(x)))
    elif name == "seseman":
        assert all(sum(x[i] for i in side) == 9 for side in [(0, 1, 2), (0, 3, 5), (2, 4, 7), (5, 6, 7)])
    elif name == "rabbits":
        assert values == {"rabbits": 3, "pheasants": 6}
    elif name == "schedule1":
        starts = [values[f"s{i}"] for i in range(7)]
        ends = [s + d for s, d in zip(starts, data["duration"])]
        area = sum(d * r for d, r in zip(data["duration"], data["resource"]))
        lower_bound = 1 + (area + data["capacity"] - 1) // data["capacity"]
        assert max(ends) == values["makespan"] == lower_bound == 23
        for time in range(1, max(ends)):
            assert sum(r for s, e, r in zip(starts, ends, data["resource"]) if s <= time < e) <= data["capacity"]
    elif name == "discrete_tomography":
        rows, cols = len(data["rows"]), len(data["cols"])
        assert [sum(x[i * cols : (i + 1) * cols]) for i in range(rows)] == data["rows"]
        assert [sum(x[j::cols]) for j in range(cols)] == data["cols"]
    elif name == "traffic_lights":
        allowed = {tuple(row) for row in data["allowed"]}
        for i in range(4):
            j = (i + 1) % 4
            assert (values[f"v{i}"], values[f"p{i}"], values[f"v{j}"], values[f"p{j}"]) in allowed
    elif name == "nvalue":
        assert values["count"] == len(set(x))
    else:
        raise AssertionError(f"No independent checker for {name}")


@pytest.mark.parametrize("name", ENTRIES)
def test_hakank_model_synthesizes_a_valid_assignment(name):
    pytest.importorskip("ortools", reason="synthesis-ortools extra")
    entry = ENTRIES[name]
    driver = AeonDriver(AeonConfig("ortools", SilentSynthesisUI(), 10, no_main=True))
    assert not list(driver.parse(filename=str(SUITE / f"{name}.ae")))
    assert driver.has_synth()
    driver.synth()
    assert not driver.has_synth()
    definitions = {binding.var_name.name: binding for binding in iterate_top_level(driver.core)}
    values = {}
    for variable, (lo, hi) in entry["variables"].items():
        term = definitions[variable].var_value
        assert isinstance(term, Literal), (variable, term)
        assert type(term.value) is int and lo <= term.value <= hi
        values[variable] = term.value
    check_assignment(name, values, entry["data"])
    score_name = definitions["score"].var_name
    assert aeon_eval(set_program_tail(driver.core, Var(score_name)), driver.evaluation_ctx) == entry["expected_score"]
