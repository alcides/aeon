"""Check global predicates and exact fixed-width bit-vector semantics."""

import pytest

from scripts.generate_hakank_globals import models
from tests.ortools_cpsat_test import _parse, _solve, _values


@pytest.mark.parametrize("model", models(), ids=lambda model: model.name)
def test_global(model):
    result = _values(_solve(_parse(model.render({"source_url": "https://example.org/fixture"}))))
    values = {name.removeprefix("h_"): value for name, value in result.items()}
    xs = [values[f"x{i}"] for i in range(sum(name.startswith("x") for name in values))]
    if model.name == "allequal":
        assert len(set(xs)) == 1
    elif model.name == "exactly":
        assert xs.count(values["value"]) == values["occurrences"]
    elif model.name == "globalcardinality":
        assert [xs.count(i) for i in range(1, 6)] == [4, 1, 0, 0, 0]
    elif model.name == "inverse":
        assert set(xs) == set(range(1, 7))
        assert all(xs[xs[i] - 1] == i + 1 for i in range(6))
    elif model.name == "derangement":
        assert set(xs) == set(range(1, 6))
        assert all(value != i + 1 for i, value in enumerate(xs))
    elif model.name == "notallequal":
        assert len(set(xs)) >= 2
    elif model.name == "arithor":
        assert all(values["value"] in pair for pair in zip(model.data["x"], model.data["y"]))
    elif model.name == "bitpatterns":
        words = {word: sum(int(values[f"{word}{i}"]) * 2**i for i in range(16)) for word in ["x", "y", "z"]}
        x, y, z = (words[word] for word in ["x", "y", "z"])

        def signed(number):
            return number if number < 2**15 else number - 2**16

        assert (y | x) == 0x49AB
        assert (((signed(y) >> 2) & 0xFFFF) ^ x) == 0x530B
        assert (((signed(z) >> 1) & 0xFFFF) & y) == 0x0883
        assert (((x << 2) & 0xFFFF) | z) == 0x1787
    else:
        raise AssertionError(model.name)
