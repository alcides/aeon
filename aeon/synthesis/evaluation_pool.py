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
from typing import Any, Callable

import multiprocess as mp

from aeon.backend.evaluator import EvaluationContext, eval
from aeon.core.terms import Let, Rec, Term, Var
from aeon.synthesis.api import InvalidIndividualException
from aeon.utils.name import Name

# A computation maps a (candidate-substituted) program to a value. It may raise
# ``InvalidIndividualException`` to signal "this candidate has no value here".
Computation = Callable[[Term], Any]

# Per-computation result statuses.
OK, INVALID, ERROR, TIMEOUT = "ok", "invalid", "error", "timeout"


def set_program_tail(term: Term, new_tail: Term) -> Term:
    """Replace the innermost body of a chain of top-level ``let``/``rec``
    bindings with ``new_tail`` (the bindings, and so everything in scope, stay)."""
    if isinstance(term, (Let, Rec)):
        return dataclasses.replace(term, body=set_program_tail(term.body, new_tail))
    return new_tail


class EvalPrimitives:
    """The building blocks a backend composes its requested computations from,
    without ever touching the raw evaluation context directly."""

    def __init__(self, evaluators: list[Callable[[Term], float]], ectx: EvaluationContext, feature_fun: Name):
        self._evaluators = evaluators
        self._ectx = ectx
        self._feature_fun = feature_fun

    @property
    def fitness(self) -> Computation:
        """Evaluate the objective(s): the list of per-goal distances."""
        evaluators = self._evaluators
        return lambda prog: [ev(prog) for ev in evaluators]

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


def _worker_main(static: tuple, task_q: Any, result_q: Any) -> None:
    replace, computations = static
    while True:
        msg = task_q.get()
        if msg is None:  # shutdown
            return
        cid, candidate = msg
        prog = replace(candidate)
        out: dict[str, tuple[str, Any]] = {}
        for name, comp in computations.items():
            try:
                out[name] = (OK, comp(prog))
            except InvalidIndividualException:
                out[name] = (INVALID, None)
            except Exception as e:  # noqa: BLE001 — any failure means "no value here"
                out[name] = (ERROR, f"{type(e).__name__}: {e}")
        result_q.put((cid, out))


@dataclasses.dataclass
class _Worker:
    proc: Any
    task_q: Any
    result_q: Any


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
        task_q, result_q = mp.Queue(), mp.Queue()
        proc = mp.Process(target=_worker_main, args=(self._static, task_q, result_q), daemon=True)
        proc.start()
        return _Worker(proc, task_q, result_q)

    def _recycle(self, w: _Worker) -> None:
        try:
            w.proc.terminate()
            w.proc.join(timeout=1)
        except Exception:
            pass
        fresh = self._spawn()
        w.proc, w.task_q, w.result_q = fresh.proc, fresh.task_q, fresh.result_q

    def _timeout(self) -> dict[str, tuple[str, Any]]:
        return {name: (TIMEOUT, None) for name in self._names}

    def map(self, terms: list[Term]) -> list[dict[str, tuple[str, Any]]]:
        """Run every computation on each term, returning one ``{name: (status,
        value)}`` map per term. Terms are processed in batches of ``n_workers``
        in parallel; a worker that does not answer within the budget is recycled
        and its term reported as a timeout for every computation."""
        results: list[dict[str, tuple[str, Any]]] = [self._timeout() for _ in terms]
        for base in range(0, len(terms), self._n):
            dispatched: list[tuple[int, _Worker]] = []
            for offset, term in enumerate(terms[base : base + self._n]):
                w = self._workers[offset]
                self._counter += 1
                w.task_q.put((self._counter, term))
                dispatched.append((base + offset, w))
            for idx, w in dispatched:
                try:
                    _cid, out = w.result_q.get(timeout=self._budget + 1.0)
                    results[idx] = out
                except Exception:
                    self._recycle(w)
                    results[idx] = self._timeout()
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
                if w.proc.is_alive():
                    w.proc.terminate()
            except Exception:
                pass
