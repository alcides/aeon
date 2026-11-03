"""Specification adapters shared by synthesis backends.

Examples and property failures have the known target zero. CSV squared error
can also be checked for zero, but this deliberately restricts a satisfaction
backend to exact fits. General objectives have no such target.
"""

from collections.abc import Callable

from aeon.core.terms import Term
from aeon.synthesis.api import UnsupportedSynthesisGoal
from aeon.synthesis.decorators import Goal
from aeon.synthesis.evaluation_pool import EvaluationPool, OK


CHECKABLE_GOALS = frozenset({"example", "csv", "property", "constraint"})


def require_checkable(goals: list[Goal], backend: object) -> None:
    if getattr(backend, "supports_candidate_enumeration", False):
        return
    if any(goal.kind not in CHECKABLE_GOALS for goal in goals):
        raise UnsupportedSynthesisGoal(
            f"{type(backend).__name__} cannot optimize arbitrary minimize/maximize goals; "
            "use an optimization backend such as enumerative, random_search or gp. "
            "Examples, properties and exact-fit CSV data can be validated instead."
        )


def checked_validator(
    validate: Callable[[Term], bool], pool: EvaluationPool, computation: str = "specification"
) -> Callable[[Term], bool]:
    """Keep the refinement proof and require every additional check to pass.

    The shared worker timeout contains divergent candidate evaluations. A failed
    check is ordinary rejection, allowing the backend to try its next candidate.
    """

    def checked(candidate: Term) -> bool:
        if not validate(candidate):
            return False
        status, scores = pool.run(candidate).get(computation, ("error", None))
        return status == OK and isinstance(scores, list) and bool(scores) and all(score == 0 for score in scores)

    return checked
