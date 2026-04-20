from __future__ import annotations

from dataclasses import dataclass

from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.typechecking.context import TypingContext


@dataclass
class TacticState:
    """Typing context for the synthesis goal plus the current partial core term."""

    ctx: TypingContext
    term: Term
    goal: Type
