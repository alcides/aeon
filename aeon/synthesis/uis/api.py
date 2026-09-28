import abc
import json
from enum import Enum
from typing import Any, Sequence

from aeon.backend.evaluator import EvaluationContext
from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.sugar.program import STerm
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name
from aeon.utils.pprint import pretty_print_sterm

# Maximum Pareto members shown in the terminal UI; larger fronts are sampled.
PARETO_DISPLAY_LIMIT = 10


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

    def register_front(
        self,
        front: Sequence[tuple[Any, Term | None]],
        elapsed_time: float,
    ) -> None:
        """Report the current Pareto archive ``[(quality, term), ...]``.

        Default is a no-op. Terminal UIs show every member, or a random sample
        of :data:`PARETO_DISPLAY_LIMIT` when the front is larger.
        """
        return None

    def progress(self, created: int, assessed: int, elapsed_time: float) -> None:
        """Optional: report cumulative search counts so far -- ``created`` is the
        number of candidate programs generated, ``assessed`` the number actually
        evaluated/validated. Backends call this periodically; UIs that do not
        surface counts (terminal, silent) ignore it (the default is a no-op)."""
        return None

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
                result = {
                    f"?{name.pretty()}": pretty_print_sterm(terms[name]) if name in terms else "None" for name in terms
                }
                print(json.dumps(result, indent=2))

            case _:
                for name in terms:
                    name_str = name.pretty()
                    term_str = pretty_print_sterm(terms[name]) if name in terms else "None"
                    print(f"?{name_str}: {term_str}")
        # print()
        # pretty_print_term(synthesis_result, 200)


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
