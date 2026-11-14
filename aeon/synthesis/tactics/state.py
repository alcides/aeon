from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, replace

from aeon.core.terms import Annotation, Term
from aeon.core.types import Type
from aeon.typechecking.context import TypingContext
from aeon.typechecking.linearity import check_linearity


@dataclass
class TacticState:
    """Typing context for the synthesis goal plus the current partial core term."""

    ctx: TypingContext
    term: Term
    goal: Type
    check_sketch: Callable[[Term], bool] | None = None

    def qtt_feasible(self) -> bool:
        """Holes may supply missing uses; known QTT violations cannot be repaired."""
        if self.check_sketch is not None and not self.check_sketch(self.term):
            return False
        return not check_linearity(Annotation(self.term, self.goal), self.ctx)

    def transition(self, term: Term, goal: Type | None = None) -> TacticState | None:
        """Accept a replacement only if the complete partial state remains feasible."""
        candidate = replace(self, term=term, goal=self.goal if goal is None else goal)
        return candidate if candidate.qtt_feasible() else None
