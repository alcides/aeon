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


@pytest.mark.parametrize("failure", ["crash", "stall"])
def test_partial_result_transfer_is_bounded_and_worker_recovers(failure):
    # Interrupt the child itself after a fixed prefix of its first reply.
    # A parent-side signal races with transmission: a fast worker can finish
    # before the parent's readiness notification is handled (notably on macOS).
    # Keep an outer watchdog so a broken frame timeout cannot hang pytest.
    code = """
import os, signal, struct
import aeon.synthesis.evaluation_pool as transport
from multiprocess.reduction import ForkingPickler
from aeon.core.terms import Literal
from aeon.core.types import t_int
from aeon.synthesis.evaluation_pool import EvaluationPool, TIMEOUT
send_result = transport._send_result
def interrupt_reply(channel, result):
    if result[0] == 1:
        payload = ForkingPickler.dumps(result)
        assert len(payload) > 32
        channel.sendall(struct.pack('!Q', len(payload)))
        channel.sendall(payload[:32])
        os.kill(os.getpid(), signal.SIGKILL if FAILURE == 'crash' else signal.SIGSTOP)
        raise AssertionError('interrupted worker unexpectedly resumed')
    send_result(channel, result)
transport._send_result = interrupt_reply
pool = EvaluationPool(lambda t: t, {'fitness': lambda t: b'x' * 4096 if t.value == 0 else 42}, budget_eval=.1)
try:
    assert pool.run(Literal(0, t_int))['fitness'][0] == TIMEOUT
    assert pool.run(Literal(1, t_int))['fitness'] == ('ok', 42)
finally:
    pool.close()
""".replace("FAILURE", repr(failure))
    completed = subprocess.run([sys.executable, "-c", code], capture_output=True, text=True, timeout=15)
    assert completed.returncode == 0, completed.stderr


def test_large_result_survives_multiple_socket_reads():
    data = b"result" * 200_000
    pool = EvaluationPool(lambda t: t, {"output": lambda _: data}, budget_eval=2)
    try:
        assert pool.run(Literal(0, t_int))["output"] == ("ok", data)
    finally:
        pool.close()


def test_hung_worker_does_not_expire_a_healthy_siblings_reply():
    def compute(term):
        if term.value == 0:
            time.sleep(100)
        return b"x" * 1_000_000

    pool = EvaluationPool(lambda t: t, {"output": compute}, budget_eval=0.1, n_workers=2)
    try:
        results = pool.map([Literal(0, t_int), Literal(1, t_int)])
        assert results[0]["output"][0] == TIMEOUT
        assert results[1]["output"] == ("ok", b"x" * 1_000_000)
    finally:
        pool.close()
