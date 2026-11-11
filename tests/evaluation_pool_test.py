"""Regression tests for EvaluationPool timeout/recycle/shutdown."""

from __future__ import annotations

import time
import subprocess
import sys

import pytest

from aeon.core.terms import Literal
from aeon.core.types import t_int
from aeon.synthesis.evaluation_pool import TIMEOUT, EvaluationPool


def test_pool_recycles_timed_out_workers_and_closes():
    def hang(_prog):
        time.sleep(100)

    terms = [Literal(i, t_int) for i in range(3)]
    pool = EvaluationPool(lambda t: t, {"fitness": hang}, budget_eval=0.2, n_workers=1)
    try:
        outs = pool.map(terms)
        assert [o["fitness"][0] for o in outs] == [TIMEOUT, TIMEOUT, TIMEOUT]
    finally:
        t0 = time.time()
        pool.close()
        assert time.time() - t0 < 5.0


def test_pool_evaluates_simple_fitness():
    pool = EvaluationPool(
        lambda t: t,
        {"fitness": lambda prog: [float(prog.value)]},
        budget_eval=2.0,
        n_workers=1,
    )
    try:
        out = pool.run(Literal(12, t_int))
        assert out["fitness"] == ("ok", [12.0])
    finally:
        pool.close()


@pytest.mark.parametrize("scenario", ["dead_worker", "dispatch_deadline"])
def test_worker_failures_do_not_escape_their_deadlines(scenario):
    code = """
import time
from aeon.core.terms import Literal
from aeon.core.types import t_int, t_string
from aeon.synthesis.evaluation_pool import EvaluationPool, TIMEOUT
if SCENARIO == 'dead_worker':
    pool = EvaluationPool(lambda t: t, {'fitness': lambda t: 42}, budget_eval=0.05)
    try:
        worker = pool._workers[0]
        worker.proc.kill()
        worker.proc.join()
        assert pool.run(Literal('x' * 1000000, t_string))['fitness'][0] == TIMEOUT
        assert pool.run(Literal(0, t_int))['fitness'] == ('ok', 42)
    finally:
        pool.close()
else:
    def wait(term):
        time.sleep(term.value)
        return term.value
    pool = EvaluationPool(lambda t: t, {'fitness': wait}, budget_eval=0.05, n_workers=2)
    try:
        results = pool.map([Literal(100, t_int), Literal(2, t_int)])
        assert [r['fitness'][0] for r in results] == [TIMEOUT, TIMEOUT], results
    finally:
        pool.close()
""".replace("SCENARIO", repr(scenario))
    completed = subprocess.run([sys.executable, "-c", code], capture_output=True, text=True, timeout=15)
    assert completed.returncode == 0, completed.stderr
