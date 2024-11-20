from typing import Any
from aeon.backend.evaluator import EvaluationContext
from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext


class TerminalUI(SynthesisUI):

    def start(
        self,
        typing_ctx: TypingContext,
        evaluation_ctx: EvaluationContext,
        target_name: str,
        target_type: Type,
        budget: Any,
    ):
        self.target_name = target_name
        self.target_type = target_type
        self.budget = budget

    def register(
        self,
        solution: Term,
        quality: Any,
        elapsed_time: float,
        is_best: bool,
    ):
        if is_best:
            self.best_solution = solution
            self.best_quality = quality

        print(
            f"Target: {self.target_name} ({elapsed_time:.1f} / {self.budget:.1f}s) "
            + f"| Best: {self.best_solution} ({self.best_quality}) " +
            f"| Current: {solution} ({quality})", )

    def end(self, solution: Term, quality: Any):
        pass
