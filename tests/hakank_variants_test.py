"""Alternate encodings must retain their mathematical goals and actual clues."""

import pytest

from scripts.generate_hakank_variants import models
from tests.hakank_cp_examples_test import check_assignment
from tests.ortools_cpsat_test import _parse, _solve, _values


@pytest.mark.parametrize("model", models(), ids=lambda model: model.name)
def test_variant(model):
    values = _values(_solve(_parse(model.render({"source_url": "https://example.org/fixture"})), budget=20))
    values = {name.removeprefix("h_"): value for name, value in values.items()}
    if model.name.startswith("sudoku"):
        n = model.data["size"]
        grid = [[values[f"x{r * n + c}"] for c in range(n)] for r in range(n)]
        target = set(range(1, n + 1))
        assert all(set(row) == target for row in grid)
        assert all({grid[r][c] for r in range(n)} == target for c in range(n))
        block = int(n**0.5)
        for row in range(0, n, block):
            for column in range(0, n, block):
                assert {grid[row + r][column + c] for r in range(block) for c in range(block)} == target
        assert all(
            grid[r][c] == model.data["clues"][r][c] for r in range(n) for c in range(n) if model.data["clues"][r][c]
        )
    elif model.name == "donaldgerald":
        assert len(set(values.values())) == 10

        def word(text):
            return int("".join(str(values[letter]) for letter in text))

        assert word("donald") + word("gerald") == word("robert")
    elif model.name == "alldifferentexcept0test":
        sequence = list(values.values())
        assert sequence == sorted(sequence)
        assert len([v for v in sequence if v]) == len({v for v in sequence if v})
    else:
        check_assignment(model.data["specification_of"], values, model.data)
