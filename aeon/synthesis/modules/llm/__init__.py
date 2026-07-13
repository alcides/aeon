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

from aeon.synthesis.modules.llm.ollama_manager import prepare_ollama_model, release_ollama_model


# Curated Ollama tags for code synthesis on Apple Silicon with ≤64 GB unified memory.
# Footprints are approximate Q4_K_M sizes; all run comfortably on an M1 Pro/Max.
LLM_OLLAMA_MODELS: dict[str, str] = {
    # ~20 GB — strongest open coder in this class; default for ``-s llm``.
    "llm_qwen2.5-coder-32b": "qwen2.5-coder:32b",
    # ~9 GB — best speed/quality trade-off for interactive synthesis.
    "llm_qwen2.5-coder-14b": "qwen2.5-coder:14b",
    # ~10 GB — MoE coder; strong on multi-language benchmarks.
    "llm_deepseek-coder-v2-16b": "deepseek-coder-v2:16b",
    # ~8 GB — reliable general-purpose code baseline.
    "llm_codellama-13b": "codellama:13b",
    # ~9 GB — multilingual code; good library/API completion.
    "llm_starcoder2-15b": "starcoder2:15b",
    # ~4 GB — lightweight; fast iteration when the hole is small.
    "llm_deepseek-coder-6.7b": "deepseek-coder:6.7b",
}

DEFAULT_LLM_SYNTHESIZER_ID = "llm_qwen2.5-coder-32b"

# Backward-compatible CLI id (``-s llm``) → default model above.
LLM_OLLAMA_MODELS["llm"] = LLM_OLLAMA_MODELS[DEFAULT_LLM_SYNTHESIZER_ID]


def llm_synthesizer_menu_ids() -> list[str]:
    """Synthesizer ids shown in the LSP/infoview menus (one entry per model)."""
    return [sid for sid in LLM_OLLAMA_MODELS if sid != "llm"]


def llm_synthesizer_label(synthesizer_id: str) -> str:
    """Display label with the Ollama model tag visible in menus."""
    model = LLM_OLLAMA_MODELS.get(synthesizer_id, synthesizer_id)
    return f"LLM generation ({model})"


def is_llm_synthesizer(synthesizer_id: str) -> bool:
    return synthesizer_id in LLM_OLLAMA_MODELS


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
    def __init__(self, model: str = LLM_OLLAMA_MODELS[DEFAULT_LLM_SYNTHESIZER_ID]):
        self.model = model

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
        best_quality = None

        goals: list[Goal] = current_metadata.get("goals", [])
        minimize_list = [goal.minimize for goal in goals for _ in range(goal.length)]
        prompt = current_metadata.get("prompt", "Any program")

        start_time = monotonic_ns()
        temperature = 0.0
        try:
            prepare_ollama_model(self.model)
            while get_elapsed_time(start_time) <= budget:
                result = generate(
                    model=self.model, prompt=f"{system_prompt}\n{prompt}", options={"temperature": temperature}
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
                    temperature += 0.2
        finally:
            release_ollama_model(self.model)
        return core_term
