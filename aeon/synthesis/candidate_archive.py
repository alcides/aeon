"""Budgeted Pareto selection for backends that enumerate feasible programs."""

from math import isfinite
from time import monotonic

from aeon.core.terms import Term
from aeon.synthesis.api import (
    InvalidIndividualException,
    SynthesisNotSuccessful,
    TimeoutInEvaluationException,
    UnsupportedSynthesisGoal,
)
from aeon.synthesis.pareto import minimize_flags_from_goals, pick_pareto_member, update_pareto_front
from aeon.synthesis.specifications import CHECKABLE_GOALS


class CandidateArchive:
    """Keep search acceptance separate from the decision to stop searching.

    Call ``consider`` only after validation. Its return value means *stop*,
    not *valid*: numerical objectives keep search running. The complete archive
    is available as ``backend.pareto_front`` and through ``ui.register_front``.
    """

    def __init__(self, backend, fun_name, metadata, evaluate, budget, ui):
        self.backend = backend
        self.backend.pareto_front = []
        goals = metadata.get(fun_name, {}).get("goals", [])
        self.optimizing = any(g.kind not in CHECKABLE_GOALS for g in goals)
        self.flags = minimize_flags_from_goals(goals)
        self.evaluate = evaluate
        self.ui = ui
        self.started = monotonic()
        self.deadline = self.started + max(0.0, budget)
        self.seen: set[str] = set()
        self.first: Term | None = None

    @property
    def expired(self):
        return monotonic() >= self.deadline

    def consider(self, candidate: Term) -> bool:
        if not self.optimizing:
            self.first = candidate
            self.ui.register(candidate, [], monotonic() - self.started, True)
            return True
        key = str(candidate)
        if key in self.seen or self.expired:
            return False
        self.seen.add(key)
        try:
            scores = self.evaluate(candidate)
        except (InvalidIndividualException, TimeoutInEvaluationException):
            return False
        if len(scores) != len(self.flags):
            raise ValueError(f"Expected {len(self.flags)} objective values, got {len(scores)}")
        if not all(isfinite(score) for score in scores):
            return False
        front, changed = update_pareto_front(self.backend.pareto_front, scores, candidate, self.flags)
        self.backend.pareto_front = front
        elapsed = monotonic() - self.started
        self.ui.register(candidate, scores, elapsed, changed)
        if changed:
            self.ui.register_front(list(front), elapsed)
        return False

    def result(self) -> Term | None:
        front = self.backend.pareto_front
        if front:
            self.ui.register_front(list(front), monotonic() - self.started)
            return pick_pareto_member(front, getattr(self.backend, "seed", 0))
        return self.first

    def search(self, candidates, validate) -> Term | None:
        """Consume a candidate iterator, retaining incumbents on budget exhaustion."""
        try:
            for candidate in candidates:
                if self.expired:
                    break
                if validate(candidate) and self.consider(candidate):
                    break
        except UnsupportedSynthesisGoal:
            raise
        except SynthesisNotSuccessful:
            if not self.backend.pareto_front and self.first is None:
                raise
        finally:
            close = getattr(candidates, "close", None)
            if close is not None:
                close()
        return self.result()
