from typing import Callable
from time import monotonic_ns

from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name
from aeon.sugar.parser import parse_expression
from aeon.core.terms import Hole
from aeon.sugar.lowering import lower_to_core
from aeon.synthesis.decorators import Goal

from ollama import generate


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


class LLMSynthesizer(Synthesizer):
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

        var_description = ", ".join([f"{name} : {ty}" for (name, ty) in ctx.concrete_vars()])

        system_prompt = (
            "Please generate a candidate expression for the problem defined after the word PROBLEM."
            f"The candidate expression should be an expression of type {type}, and"
            "be written in the aeon programming language."
            "Aeon is a functional programming language, with a syntax very similar to Haskell, but with colons like ML."
            "Aeon has first-class refinement types, but unlike LiquidHaskell, those are not presented as comments, but rather directly in types."
            "Present the expression directly, with no explanation or code around it."
            "Presente the expression as you would enter it in an interpreter, without top-level declarations or type annotations."
            f"In the expression, you can use the following variables: {var_description}"
            "\n"
            "\nPROBLEM:"
        )
        core_term: Term = Hole(Name("sorry", -1))
        best_quality = None

        current_metadata = metadata.get(fun_name, {})
        goals: list[Goal] = current_metadata.get("goals", [])
        minimize_list = [goal.minimize for goal in goals for _ in range(goal.length)]
        prompt = current_metadata.get("prompt", "Any program")

        start_time = monotonic_ns()
        temperature = 0.0
        while get_elapsed_time(start_time) <= budget:
            result = generate(
                model="qwen2.5:32b", prompt=f"{system_prompt}\n{prompt}```", options={"temperature": temperature}
            )
            r = result.response
            try:
                tterm = parse_expression(f"({r})")
                core_tterm = lower_to_core(tterm)

                if validate(core_tterm):
                    quality = evaluate(core_tterm)
                    if len(quality) == 0:
                        return core_tterm
                    time = get_elapsed_time(start_time)
                    is_best = is_better(quality, best_quality, minimize_list)
                    ui.register(core_tterm, quality, time, is_best)
                    if is_best:
                        core_term = core_tterm
                        best_quality = quality
                else:
                    time = get_elapsed_time(start_time)
                    ui.register(core_tterm, None, time, False)

            except Exception:
                temperature += 0.1
        return core_term
