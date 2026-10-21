"""Unserializable output must not drop the worker's complete reply."""

import ctypes
import subprocess
import sys
import time

import pytest

from aeon.core.terms import Literal
from aeon.core.types import t_int
from aeon.synthesis.evaluation_pool import ERROR, OK, EvaluationPool


def test_unserializable_feature_preserves_fitness_and_worker():
    pool = EvaluationPool(
        lambda term: term,
        {"fitness": lambda term: [float(term.value)], "output": lambda term: ctypes.pointer(ctypes.c_int(1))},
        budget_eval=2,
    )
    try:
        pid = pool._workers[0].proc.pid
        started = time.monotonic()
        for value in (1, 2):
            result = pool.run(Literal(value, t_int))
            assert result["fitness"] == (OK, [float(value)])
            assert result["output"][0] == ERROR
            assert "cannot be pickled" in result["output"][1]
            assert pool._workers[0].proc.pid == pid
        assert time.monotonic() - started < 2
    finally:
        pool.close()


@pytest.mark.parametrize(
    "case",
    [
        "examples/synthesis/cata/mutual_pbe.ae",
        "examples/synthesis/cata/synth/mr/even_odd.ae",
        "examples/synthesis/cata/synth/mr/even_odd2.ae",
        "examples/talk/05_mutual_examples.ae",
    ],
)
def test_mutual_symetric_does_not_lose_output_responses(case):
    result = subprocess.run(
        [sys.executable, "-m", "aeon", "--no-main", "-s", "symetric", "--budget", "1", case],
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert result.returncode in (0, 2), result.stderr
    assert "ctypes objects containing pointers cannot be pickled" not in result.stderr
    assert "Traceback" not in result.stderr
