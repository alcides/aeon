from time import monotonic_ns
from typing import Any, Callable

from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer
from aeon.synthesis.modules.synquid.build import synthes_memory
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def is_better(v1, v2):
    if v2[0] < 0:
        return True
    return all(x < y for x, y in zip(v1, v2))


def get_elapsed_time(start_time) -> float:
    """The elapsed time since the start in seconds."""
    return (monotonic_ns() - start_time) * 0.000000001


class SynquidSynthesizer(Synthesizer):
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

        current_metadata = metadata.get(fun_name, {})
        is_recursion_allowed = current_metadata.get("recursion", False)
        vars_to_ignore = current_metadata.get("hide", [])

        def skip(name: Name) -> bool:
            if name == fun_name:
                return not is_recursion_allowed
            elif name in vars_to_ignore:
                return True
            elif name.name.startswith("__internal__"):
                return True
            elif name.name in ["native", "native_import", "print"]:
                return True
            else:
                return False

        start_time = monotonic_ns()
        done = True
        level = 0
        best: tuple[list[float], Any] = ([-1], None)
        mem: dict = {}
        while done:
            for result in synthes_memory(ctx, level, type, skip, mem):
                if validate(result):
                    score = evaluate(result)
                    if is_better(score, best[0]):
                        best = (score, result)
                        ui.register(result, score, get_elapsed_time(start_time), True)
                    else:
                        ui.register(result, score, get_elapsed_time(start_time), False)
                if get_elapsed_time(start_time) > budget:
                    done = False
                    break
            level += 1
        return best[1]
