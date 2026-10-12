"""Check native catalogue ports using separate mathematical representations."""

from itertools import combinations, product
from math import isqrt

import pytest

from scripts.generate_hakank_manual import models
from tests.ortools_cpsat_test import _parse, _solve, _values


@pytest.mark.parametrize("model", models(), ids=lambda model: model.name)
def test_manual_model(model):
    values = _values(_solve(_parse(model.render({"source_url": "https://example.org/fixture"})), budget=20))
    x = {name.removeprefix("h_"): value for name, value in values.items()}
    if model.name == "12packproblem":
        assert x["bottles"] == 7 * x["pack0"] + 13 * x["pack1"] >= 20
        reference = min(7 * a + 13 * b for a, b in product(range(4), repeat=2) if 7 * a + 13 * b >= 20)
        assert x["bottles"] == reference
    elif model.name == "17b":
        for r1, r2 in combinations(range(4), 2):
            for c1, c2 in combinations(range(4), 2):
                assert len({x[f"cell{r * 4 + c}"] for r in (r1, r2) for c in (c1, c2)}) > 1
    elif model.name == "donaldgeraldrobert":
        assert len(set(x.values())) == 10

        def word(text):
            return int("".join(str(x[letter]) for letter in text))

        assert all(x[letter] > 0 for letter in "dgr")
        assert word("donald") + word("gerald") == word("robert")
    elif model.name == "magichexagon":
        assert set(x.values()) == set(range(1, 20))
        assert all(sum(x[letter] for letter in line) == 38 for line in model.data["lines"])
    elif model.name == "eq20":
        assert all(
            sum(coefficient * x[f"x{i}"] for i, coefficient in enumerate(row)) == target
            for row, target in zip(model.data["matrix"], model.data["targets"])
        )
    elif model.name == "alldifferentreif":
        sequence = [x[f"x{i}"] for i in range(4)]
        assert sequence == sorted(sequence)
        assert x["distinct"] == (len(set(sequence)) == len(sequence))
    elif model.name == "bowlsandoranges":
        positions = [x[f"bowl{i}"] for i in range(9)]
        assert positions == sorted(set(positions))
        assert all(b - a != c - b for a, b, c in combinations(positions, 3))
    elif model.name == "2012cmoproblem":
        prime = x["a"] - x["b"]
        assert prime >= 2 and all(prime % d for d in range(2, isqrt(prime) + 1))
        assert x["a"] * x["b"] == x["n"] ** 2
        reference = next(
            a
            for a in range(2012, 2026)
            if any(
                a - b >= 2 and all((a - b) % d for d in range(2, isqrt(a - b) + 1)) and isqrt(a * b) ** 2 == a * b
                for b in range(2, min(a, 2012) + 1)
            )
        )
        assert x["a"] == reference
    else:
        raise AssertionError(model.name)
