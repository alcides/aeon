import abc
from typing import Any

from aeon.backend.evaluator import EvaluationContext
from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.typechecking.context import TypingContext


class SynthesisUI(abc.ABC):

    def start(
        self,
        typing_ctx: TypingContext,
        evaluation_ctx: EvaluationContext,
        target_name: str,
        target_type: Type,
        budget: Any,
    ):
        ...

    def register(self, solution: Term, quality: Any, elapsed_time: float,
                 is_best: bool):
        ...

    def end(self, solution: Term, quality: Any):
        ...


class SilentSynthesisUI(SynthesisUI):

    def start(
        self,
        typing_ctx: TypingContext,
        evaluation_ctx: EvaluationContext,
        target_name: str,
        target_type: Type,
        budget: Any,
    ):
        pass

    def register(self, solution: Term, quality: Any, elapsed_time: float,
                 is_best: bool):
        pass

    def end(self, solution: Term, quality: Any):
        pass
