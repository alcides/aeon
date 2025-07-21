import abc
import json
from enum import Enum
from typing import Any

from aeon.backend.evaluator import EvaluationContext
from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.sugar.program import STerm
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name
from aeon.utils.pprint_helpers import pretty_print


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

    def display_results(
        self,
        program: Term,
        terms: dict[Name, STerm],
        synthesis_format: SynthesisFormat = SynthesisFormat.DEFAULT,
    ):
        print("Synthesized holes:")
        match synthesis_format:
            case SynthesisFormat.JSON:
                result = {f"?{name.pretty()}": pretty_print(terms[name]) if name in terms else "None" for name in terms}
                print(json.dumps(result, indent=2))

            case _:
                for name in terms:
                    name_str = name.pretty()
                    term_str = pretty_print(terms[name]) if name in terms else "None"
                    print(f"?{name_str}: {term_str}")
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
