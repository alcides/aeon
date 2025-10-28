from typing import Callable
from time import monotonic_ns

from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name
from aeon.core.terms import Hole


def get_elapsed_time(start_time) -> float:
    """The elapsed time since the start in seconds."""
    return (monotonic_ns() - start_time) * 0.000000001


def is_better(a: list[float], b: list[float] | None, minimize: list[bool]) -> bool:
    if b is None:
        return True
    wins = 0
    losses = 0
    for ai, bi, min in zip(a, b, minimize):
        if min:
            if ai <= bi:
                wins += 1
            else:
                losses += 1
        else:
            if ai >= bi:
                wins += 1
            else:
                losses += 1
    return wins - losses > 0


class SMTSynthesizer(Synthesizer):
    def synthesize(
        self,
        ctx: TypingContext,
        type: Type,
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        fun_name: Name,
        metadata: Metadata,
        budget: float = 60,
        ui: SynthesisUI = SynthesisUI(),
    ) -> Term:
        assert isinstance(ctx, TypingContext)
        assert isinstance(type, Type)

        core_term: Term = Hole(Name("sorry", -1))
        return core_term
