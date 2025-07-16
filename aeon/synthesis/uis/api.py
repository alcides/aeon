import abc
import json
from enum import Enum
from typing import Any

from aeon.backend.evaluator import EvaluationContext
from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


class SynthesisFormat(Enum):
    DEFAULT = "default"
    JSON = "json"

    @classmethod
    def from_string(cls, string_value):
        for member in cls:
            if member.value == string_value:
                return member
        return cls.DEFAULT


class SynthesisUI(abc.ABC):
    def start(
        self,
        typing_ctx: TypingContext,
        evaluation_ctx: EvaluationContext,
        target_name: str,
        target_type: Type | None,
        budget: Any,
    ): ...

    def register(
        self,
        solution: Term,
        quality: Any,
        elapsed_time: float,
        is_best: bool,
    ): ...

    def end(self, solution: Term, quality: Any): ...

    def wrapper(self, f):
        """This wrapper is necessary for the NCurses version of the API"""
        return f()

    def display_results(
        self,
        program: Term,
        terms: dict[Name, Term],
        synthesis_format: SynthesisFormat = SynthesisFormat.DEFAULT,
    ):
        match synthesis_format:
            case SynthesisFormat.JSON:
                result = {
                    "synthesized_holes": {f"?{str(name)}": str(terms[name]) for name in terms},
                }
                print(json.dumps(result, indent=2))

            case _:
                print("Synthesized holes:")
                for name in terms:
                    print(f"?{name}: {terms[name]}")
        # print()
        # pretty_print_term(ensure_anf(synthesis_result, 200))


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

    def register(
        self,
        solution: Term,
        quality: Any,
        elapsed_time: float,
        is_best: bool,
    ):
        pass

    def end(self, solution: Term, quality: Any):
        pass
