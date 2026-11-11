"""A pool of persistent worker processes that run computations on candidates.

Evaluating a candidate in a fresh process each time (the simple ``make_evaluator``
in ``entrypoint.py``) pays a process spawn/teardown and re-pickles the whole
program every call. Across the thousands of candidates a search evaluates, that
overhead dominates.

``EvaluationPool`` keeps a small set of workers alive and is *computation
agnostic*: it is built with a dict of named ``Computation``s -- functions of the
substituted program -- and returns, for each candidate, a ``{name: (status,
value)}`` map computed in a single round-trip. It does not know what those
computations mean; a backend decides which to request (a fitness distance, an
output/scene feature for clustering, or anything else) via
``Synthesizer.computations``. A candidate that hangs is still contained: a
per-task timeout kills and replaces its worker.
"""

from __future__ import annotations

import dataclasses
import os
import socket
import struct
from selectors import DefaultSelector, EVENT_READ
from time import monotonic
from typing import Any, Callable, Optional

import multiprocess as mp
from multiprocess.reduction import ForkingPickler

from aeon.backend.evaluator import EvaluationContext, eval
from aeon.core.terms import Term, Var
from aeon.synthesis.api import InvalidIndividualException
from aeon.synthesis.fitness_eval import (
    memoize_fitness,
    set_program_tail,
    require_complete_program,
    without_main_placeholder,
)
from aeon.utils.name import Name

# A computation maps a (candidate-substituted) program to a value. It may raise
# ``InvalidIndividualException`` to signal "this candidate has no value here".
Computation = Callable[[Term], Any]

# Per-computation result statuses.
OK, INVALID, ERROR, TIMEOUT = "ok", "invalid", "error", "timeout"

# Fork inherits the parent's address space, so the (often large, closure-heavy)
# replace/computations payload need not be picklable. Spawn was tried to avoid
# fork-after-threads deadlocks, but under CI load it made every eval time out.
# We keep fork and tear queues/processes down hard on recycle so abandoned
# Queue feeder threads cannot accumulate and later deadlock ``Process.start``.
_CTX = mp.get_context("fork")


class EvalPrimitives:
    """The building blocks a backend composes its requested computations from,
    without ever touching the raw evaluation context directly."""

    def __init__(
        self,
        evaluators: list[Callable[[Term], list[float]]],
        ectx: EvaluationContext,
        feature_fun: Name,
        replace: Optional[Callable[[Term], Term]] = None,
        bundled_fitness: Optional[Computation] = None,
    ):
        self._evaluators = evaluators
        self._ectx = ectx
        self._feature_fun = feature_fun
        self._replace = replace
        self._bundled_fitness = bundled_fitness

    @property
    def ectx(self) -> EvaluationContext:
        """The evaluation context (prelude + program bindings). Exposed so a
        backend can evaluate candidate sub-programs directly — e.g. the FTA
        backend observing a candidate's output on concrete example inputs."""
        return self._ectx

    @property
    def replace(self) -> Optional[Callable[[Term], Term]]:
        """Fills the hole in the whole program with a given term. Exposed so a
        backend can evaluate a sub-program *in the program's context* (with all
        top-level definitions, e.g. library primitives, in scope) by replacing
        the program tail — see the FTA backend's example-driven observation."""
        return self._replace

    @property
    def fitness(self) -> Computation:
        """Evaluate the objective(s): the flat list of per-goal distances.

        Each evaluator may return one or more floats (multi-objective goals
        expand a native ``Array`` into ``goal.length`` components).
        """
        if self._bundled_fitness is not None:
            return memoize_fitness(self._bundled_fitness)
        evaluators = self._evaluators
        return memoize_fitness(lambda prog: [score for ev in evaluators for score in ev(prog)])

    @property
    def feature(self) -> Computation:
        """The candidate's output feature -- the ``@cluster`` featuriser applied
        to it, or its own value when there is no featuriser."""
        return self.eval_function(self._feature_fun)

    def eval_function(self, fun: Name) -> Computation:
        """Evaluate the program function ``fun`` applied to the candidate (by
        making it the program's result)."""
        ectx = self._ectx
        return lambda prog: eval(set_program_tail(prog, Var(fun)), ectx)


def _send_result(channel: socket.socket, result: Any) -> None:
    payload = ForkingPickler.dumps(result)
    channel.sendall(struct.pack("!Q", len(payload)))
    channel.sendall(payload)


@dataclasses.dataclass
class _ResultReader:
    """Incrementally receive a frame without blocking on a partial reply."""

    size: int | None = None
    data: bytearray = dataclasses.field(default_factory=bytearray)

    def read(self, channel: socket.socket) -> Any:
        remaining = (8 if self.size is None else self.size) - len(self.data)
        block = channel.recv(min(remaining, 65536))
        if not block:
            raise EOFError("worker closed an incomplete result")
        self.data.extend(block)
        if self.size is None and len(self.data) == 8:
            self.size = struct.unpack("!Q", self.data)[0]
            self.data.clear()
        elif self.size is not None and len(self.data) == self.size:
            return ForkingPickler.loads(self.data)
        return None


def _worker_main(static: tuple, task_q: Any, result: socket.socket, parent_result: socket.socket) -> None:
    parent_result.close()
    try:
        _worker_loop(static, task_q, result)
    finally:
        result.close()


def _worker_loop(static: tuple, task_q: Any, result: socket.socket) -> None:
    replace, computations = static
    while True:
        msg = task_q.get()
        if msg is None:  # shutdown
            return
        cid, candidate = msg
        try:
            prog = without_main_placeholder(replace(candidate))
            require_complete_program(prog)
        except InvalidIndividualException:
            _send_result(result, (cid, monotonic(), {name: (INVALID, None) for name in computations}))
            continue
        except Exception as exc:
            _send_result(
                result, (cid, monotonic(), {name: (ERROR, f"{type(exc).__name__}: {exc}") for name in computations})
            )
            continue
        out: dict[str, tuple[str, Any]] = {}
        for name, comp in computations.items():
            try:
                # Serialize separately so one unpicklable computation has a
                # normal error result and successful siblings survive.
                value = bytes(ForkingPickler.dumps(comp(prog)))
                out[name] = (OK, value)
            except InvalidIndividualException:
                out[name] = (INVALID, None)
            except Exception as e:  # noqa: BLE001 — any failure means "no value here"
                out[name] = (ERROR, f"{type(e).__name__}: {e}")
        _send_result(result, (cid, monotonic(), out))


@dataclasses.dataclass
class _Worker:
    proc: Any
    task_q: Any
    result: socket.socket


def _kill_process(proc: Any) -> None:
    """Terminate a worker, escalating to kill, and always join."""
    if proc is None:
        return
    try:
        if proc.is_alive():
            proc.terminate()
            proc.join(timeout=1)
        if proc.is_alive():
            proc.kill()
        proc.join(timeout=1)
    except Exception:
        pass


def _close_queues(*queues: Any) -> None:
    """Discard pending writes after the worker has stopped, without hanging.

    A dead reader leaves the task feeder blocked on a full pipe. Drain raw
    bytes (never the queue's read lock, which a killed worker may hold) until
    the feeder exits. Bound cleanup even if serialization itself is stuck.
    These private handles belong to the fork-only multiprocess transport.
    """
    for q in queues:
        if q is None:
            continue
        try:
            q.cancel_join_thread()
            q.close()
            feeder = q._thread
            deadline = monotonic() + 1.0
            while feeder is not None and feeder.is_alive() and monotonic() < deadline:
                if q._reader.poll(0.01):
                    if not os.read(q._reader.fileno(), 65536):
                        break
                else:
                    feeder.join(timeout=0.01)
        except Exception:
            pass
        finally:
            for connection in (q._reader, q._writer):
                try:
                    connection.close()
                except OSError:
                    pass


class EvaluationPool:
    def __init__(
        self,
        replace: Callable[[Term], Term],
        computations: dict[str, Computation],
        budget_eval: float = 1.0,
        n_workers: int = 1,
    ):
        self._static = (replace, computations)
        self._names = list(computations.keys())
        self._budget = budget_eval
        self._n = max(1, n_workers)
        self._counter = 0
        self._workers: list[_Worker] = [self._spawn() for _ in range(self._n)]

    def _spawn(self) -> _Worker:
        task_q = _CTX.Queue()
        parent_result, child_result = socket.socketpair()
        # Discarding an abandoned task can close its pipe while the feeder is
        # still finishing serialization. That is expected during hard teardown.
        task_q._ignore_epipe = True
        proc = _CTX.Process(target=_worker_main, args=(self._static, task_q, child_result, parent_result), daemon=True)
        try:
            proc.start()
        except BaseException:
            parent_result.close()
            _close_queues(task_q)
            raise
        finally:
            child_result.close()
        parent_result.setblocking(False)
        return _Worker(proc, task_q, parent_result)

    def _recycle(self, w: _Worker) -> None:
        _kill_process(w.proc)
        _close_queues(w.task_q)
        w.result.close()
        fresh = self._spawn()
        w.proc, w.task_q, w.result = fresh.proc, fresh.task_q, fresh.result

    def _timeout(self) -> dict[str, tuple[str, Any]]:
        return {name: (TIMEOUT, None) for name in self._names}

    def map(self, terms: list[Term]) -> list[dict[str, tuple[str, Any]]]:
        """Run every computation on each term, returning one ``{name: (status,
        value)}`` map per term. Terms are processed in batches of ``n_workers``
        in parallel; a worker that does not answer within the budget is recycled
        and its term reported as a timeout for every computation."""
        results: list[dict[str, tuple[str, Any]]] = [self._timeout() for _ in terms]
        for base in range(0, len(terms), self._n):
            dispatched: list[tuple[int, int, _Worker, float]] = []
            for offset, term in enumerate(terms[base : base + self._n]):
                w = self._workers[offset]
                self._counter += 1
                deadline = monotonic() + self._budget + 1.0
                w.task_q.put((self._counter, term))
                dispatched.append((base + offset, self._counter, w, deadline))
            failed: list[_Worker] = []
            with DefaultSelector() as selector:
                for idx, cid, w, deadline in dispatched:
                    selector.register(w.result, EVENT_READ, (idx, cid, w, deadline, _ResultReader()))
                # Drain every worker concurrently. Waiting for a hung worker
                # first must not consume healthy siblings' receive deadlines.
                while selector.get_map():
                    deadline = min(key.data[3] for key in selector.get_map().values())
                    for key, _ in selector.select(max(0.0, deadline - monotonic())):
                        idx, cid, w, deadline, reader = key.data
                        try:
                            reply = reader.read(w.result)
                            if reply is None:
                                continue
                            received_id, finished, out = reply
                            if received_id != cid or finished > deadline or monotonic() > deadline:
                                raise TimeoutError("candidate result exceeded its dispatch deadline")
                            results[idx] = {
                                name: (status, ForkingPickler.loads(value) if status == OK else value)
                                for name, (status, value) in out.items()
                            }
                        except BlockingIOError:
                            continue
                        except Exception:
                            failed.append(w)
                        selector.unregister(key.fileobj)
                    for key in list(selector.get_map().values()):
                        if monotonic() >= key.data[3]:
                            failed.append(key.data[2])
                            selector.unregister(key.fileobj)
            # Cleanup can wait for process termination; only do it after all
            # other replies have been received or reached their own deadlines.
            for w in failed:
                self._recycle(w)
        return results

    def run(self, term: Term) -> dict[str, tuple[str, Any]]:
        return self.map([term])[0]

    def close(self) -> None:
        for w in self._workers:
            try:
                w.task_q.put(None)
            except Exception:
                pass
        for w in self._workers:
            try:
                w.proc.join(timeout=1)
            except Exception:
                pass
            _kill_process(w.proc)
            _close_queues(w.task_q)
            w.result.close()
