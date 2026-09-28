"""Regression tests for EvaluationPool timeout/recycle/shutdown."""

from __future__ import annotations

import time

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
