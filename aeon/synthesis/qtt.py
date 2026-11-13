"""QTT validation of candidates in their surrounding program sketch."""

from collections.abc import Callable
from dataclasses import dataclass

from aeon.core.terms import Term
from aeon.synthesis.api import InvalidIndividualException
from aeon.typechecking.context import TypingContext
from aeon.typechecking.linearity import check_linearity


@dataclass
class QTTValidator:
    """Expose partial-program feasibility separately from complete validation.

    Unfilled holes defer missing uses, but cannot undo a known duplicate use,
    erased runtime access, or invalid ownership transfer. Check the whole
    sketch so uses outside the synthesized expression share the same budget.
    """

    validate: Callable[[Term], bool]
    replace: Callable[[Term], Term]
    context: TypingContext

    def feasible(self, candidate: Term) -> bool:
        try:
            return not check_linearity(self.replace(candidate), self.context)
        except InvalidIndividualException:
            return False

    def __call__(self, candidate: Term) -> bool:
        return self.feasible(candidate) and self.validate(candidate)
