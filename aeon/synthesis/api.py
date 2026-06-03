from abc import ABC
from typing import Callable

from aeon.typechecking.context import TypingContext

from aeon.core.types import Type
from aeon.core.terms import Term
from aeon.utils.name import Name

from aeon.synthesis.uis.api import SynthesisUI
from aeon.decorators.api import Metadata


class SynthesisError(Exception):
    pass


class SynthesisNotSuccessful(SynthesisError):
    pass


class TimeoutInEvaluationException(SynthesisError):
    pass


class ErrorInSynthesis(SynthesisError):
    def __init__(self, inner_exception: Exception, msg: str):
        self.inner_exception = inner_exception
        self.msg = msg


class InvalidIndividualException(SynthesisError):
    """Raised by an evaluator when a candidate has no well-defined fitness
    (e.g. its evaluation throws). Backend-neutral: synthesizer adapters are
    responsible for translating this into whatever notion of "invalid
    candidate" their search framework uses.
    """


class Synthesizer(ABC):
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
        output_value: Callable[[Term], object] | None = None,
    ) -> Term: ...
