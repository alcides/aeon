"""LLM-assisted synthesizer (optional ``[llm]`` extra).

Importing this package must not require ``ollama`` — ids and labels are always
available; provider clients load lazily when synthesis runs.
"""

from __future__ import annotations

from time import monotonic_ns
from typing import Callable

from aeon.core.terms import Hole, Term
from aeon.core.types import Type
from aeon.decorators.api import Metadata
from aeon.sugar.lowering import lower_to_core
from aeon.sugar.parser import parse_expression
from aeon.synthesis.api import Synthesizer
from aeon.synthesis.decorators import Goal
from aeon.synthesis.modules.llm.ids import (
    DEFAULT_LLM_SYNTHESIZER_ID,
    LLM_OLLAMA_MODELS,
    LLM_OPENAI_SYNTHESIZER_ID,
    is_llm_synthesizer as is_llm_synthesizer,
    llm_synthesizer_label as llm_synthesizer_label,
    llm_synthesizer_menu_ids as llm_synthesizer_menu_ids,
)
from aeon.synthesis.pareto import (
    ParetoEntry,
    dominates,
    minimize_flags_from_goals,
    pick_pareto_member,
    update_pareto_front,
)
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def resolve_llm_backend(synthesizer_id: str) -> tuple[str, str]:
    """Return ``(model, provider)`` for synthesizer id ``synthesizer_id``."""
    from aeon.synthesis.modules.llm.client import default_openai_model, llm_provider

    if synthesizer_id == LLM_OPENAI_SYNTHESIZER_ID or llm_provider() == "openai":
        return default_openai_model(), "openai"
    return LLM_OLLAMA_MODELS[synthesizer_id], "ollama"


def get_elapsed_time(start_time) -> float:
    """The elapsed time since the start in seconds."""
    return (monotonic_ns() - start_time) * 0.000000001


def is_better(a: list[float], b: list[float] | None, minimize: list[bool]) -> bool:
    """Whether ``a`` should replace the current archive champion ``b``.

    Delegates to :func:`dominates` once a previous score exists. Kept as a
    named helper so LLM tests can still import it.
    """
    if b is None:
        return True
    return dominates(a, b, minimize)


class LLMSynthesizer(Synthesizer):
    def __init__(
        self,
        model: str = LLM_OLLAMA_MODELS[DEFAULT_LLM_SYNTHESIZER_ID],
        provider: str | None = None,
    ):
        self.model = model
        self.provider = provider

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
    ) -> Term:
        from aeon.synthesis.modules.llm.client import generate, llm_provider
        from aeon.synthesis.modules.llm.ollama_manager import prepare_ollama_model, release_ollama_model

        assert isinstance(ctx, TypingContext)
        assert isinstance(type, Type)

        current_metadata = metadata.get(fun_name, {})
        var_description = ", ".join([f"{name} : {ty}" for (name, ty) in ctx.concrete_vars()])

        system_prompt = (
            "Please generate a candidate expression for the problem defined after the word PROBLEM."
            f"The candidate expression should be an expression of type {type}, and "
            "be written in the aeon programming language."
            "Aeon is a functional programming language, with a syntax very similar to Haskell, but with colons like ML."
            "Aeon has first-class refinement types, but unlike LiquidHaskell, those are not presented as comments, but rather directly in types."
            "Present the expression directly, with no explanation or code around it."
            "Presente the expression as you would enter it in an interpreter, without top-level declarations or type annotations."
            f"In the expression, you can use the following variables: {var_description}"
            "\n"
            "================"
            "\nPROBLEM:```"
        )
        core_term: Term = Hole(Name("sorry", -1))
        front: list[ParetoEntry] = []

        goals: list[Goal] = current_metadata.get("goals", [])
        minimize_list = minimize_flags_from_goals(goals)
        prompt = current_metadata.get("prompt", "Any program")

        start_time = monotonic_ns()
        temperature = 0.0
        use_ollama = (self.provider or llm_provider()) == "ollama"
        try:
            if use_ollama:
                prepare_ollama_model(self.model)
            while get_elapsed_time(start_time) <= budget:
                r = generate(
                    model=self.model,
                    prompt=f"{system_prompt}\n{prompt}",
                    temperature=temperature,
                    provider=self.provider,
                )
                try:
                    tterm = parse_expression(f"({r})")
                    core_tterm = lower_to_core(tterm)

                    if validate(core_tterm):
                        quality = evaluate(core_tterm)
                        if len(quality) == 0:
                            return core_tterm
                        time = get_elapsed_time(start_time)
                        front, is_best = update_pareto_front(front, quality, core_tterm, minimize_list)
                        if is_best:
                            ui.register_front(front, time)
                            core_term = core_tterm
                        ui.register(core_tterm, quality, time, is_best)
                    else:
                        time = get_elapsed_time(start_time)
                        ui.register(core_tterm, None, time, False)

                except Exception:
                    temperature += 0.2
        finally:
            if use_ollama:
                release_ollama_model(self.model)
        if front:
            ui.register_front(front, get_elapsed_time(start_time))
            return pick_pareto_member(front, seed=0)
        return core_term
