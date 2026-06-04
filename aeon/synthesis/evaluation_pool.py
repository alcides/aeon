"""A pool of persistent worker processes for candidate evaluation.

Evaluating a candidate in a fresh process each time (the simple ``make_evaluator``
in ``entrypoint.py``) pays a process spawn/teardown and re-pickles the whole
program every call. Across the thousands of candidates a search evaluates -- and,
for a backend that clusters by output, both an objective distance *and* an
output feature per candidate -- that overhead dominates.

``EvaluationPool`` keeps a small set of workers alive: the static program
environment is pickled to each worker once, candidates stream in over a queue,
and each worker returns the ``(distance, feature)`` **pair** in a single
round-trip (the feature is computed only when a backend asks for it). A
candidate that hangs is still contained -- a per-task timeout kills and replaces
its worker -- so the sandboxing guarantee is preserved.
"""

from __future__ import annotations

import dataclasses
from typing import Any, Callable, Optional

import multiprocess as mp

from aeon.backend.evaluator import EvaluationContext, eval
from aeon.core.terms import Let, Rec, Term, Var
from aeon.synthesis.api import InvalidIndividualException
from aeon.utils.name import Name


def set_program_tail(term: Term, new_tail: Term) -> Term:
    """Replace the innermost body of a chain of top-level ``let``/``rec``
    bindings with ``new_tail`` (the bindings, and so everything in scope, stay)."""
    if isinstance(term, (Let, Rec)):
        return dataclasses.replace(term, body=set_program_tail(term.body, new_tail))
    return new_tail


# Result statuses for a single evaluation.
OK, INVALID, ERROR, TIMEOUT = "ok", "invalid", "error", "timeout"

Static = tuple  # (ectx, replace, evaluators, feature_fun, compute_feature)


def _worker_main(static: Static, task_q: Any, result_q: Any) -> None:
    ectx, replace, evaluators, feature_fun, compute_feature = static
    while True:
        msg = task_q.get()
        if msg is None:  # shutdown
            return
        cid, candidate = msg
        prog = replace(candidate)
        status = OK
        dist: Optional[list] = []
        err = ""
        try:
            dist = [ev(prog) for ev in evaluators]
        except InvalidIndividualException:
            status, dist = INVALID, None
        except Exception as e:  # noqa: BLE001 — any failure means "drop this candidate"
            status, dist, err = ERROR, None, f"{type(e).__name__}: {e}"
        feat = None
        if compute_feature:
            try:
                feat = eval(set_program_tail(prog, Var(feature_fun)), ectx)
            except Exception:  # noqa: BLE001 — a featureless candidate just has no feature
                feat = None
        result_q.put((cid, status, dist, feat, err))


@dataclasses.dataclass
class _Worker:
    proc: Any
    task_q: Any
    result_q: Any


class EvaluationPool:
    def __init__(
        self,
        ectx: EvaluationContext,
        replace: Callable[[Term], Term],
        evaluators: list[Callable[[Term], float]],
        feature_fun: Name,
        compute_feature: bool = True,
        budget_eval: float = 1.0,
        n_workers: int = 1,
    ):
        self._static: Static = (ectx, replace, evaluators, feature_fun, compute_feature)
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

    def map(self, terms: list[Term]) -> list[tuple[str, Optional[list], Any, str]]:
        """Evaluate ``terms``, returning a ``(status, distance, feature, error)``
        tuple per term. Terms are processed in batches of ``n_workers`` in
        parallel; a worker that does not answer within the budget is recycled."""
        results: list[tuple[str, Optional[list], Any, str]] = [(TIMEOUT, None, None, "")] * len(terms)
        for base in range(0, len(terms), self._n):
            dispatched: list[tuple[int, _Worker]] = []
            for offset, term in enumerate(terms[base : base + self._n]):
                w = self._workers[offset]
                self._counter += 1
                w.task_q.put((self._counter, term))
                dispatched.append((base + offset, w))
            for idx, w in dispatched:
                try:
                    _cid, status, dist, feat, err = w.result_q.get(timeout=self._budget + 1.0)
                    results[idx] = (status, dist, feat, err)
                except Exception:
                    self._recycle(w)
                    results[idx] = (TIMEOUT, None, None, "")
        return results

    def pair(self, term: Term) -> tuple[str, Optional[list], Any, str]:
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
