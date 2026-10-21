"""Unrepresentable objective values reject the candidate, not the search."""

import subprocess
import sys

import pytest

from aeon.synthesis.api import InvalidIndividualException
from aeon.synthesis.fitness_eval import as_objective_vector


@pytest.mark.parametrize(
    "value,length", [(10**10000, 1), ([10**10000], 1), ([1, 10**10000], 2)], ids=["scalar", "singleton", "vector"]
)
def test_objective_float_overflow_is_invalid_fitness(value, length):
    with pytest.raises(InvalidIndividualException):
        as_objective_vector(value, length)


@pytest.mark.parametrize("case", ["function_refined_synthesis_args", "hole_refined_synthesis"])
def test_enumeration_survives_large_integer_objectives(case):
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "aeon",
            "--no-main",
            "-s",
            "enumerative",
            "--budget",
            "5",
            f"examples/synthesis/{case}.ae",
        ],
        capture_output=True,
        text=True,
        timeout=20,
    )
    assert result.returncode in (0, 2), result.stderr
    assert "Traceback" not in result.stderr
