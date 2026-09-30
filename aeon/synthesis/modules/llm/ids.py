"""LLM synthesizer ids (no heavy provider imports)."""

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

# OpenAI-compatible backend (model from ``AEON_LLM_MODEL``, endpoint from ``AEON_LLM_BASE_URL``).
LLM_OPENAI_SYNTHESIZER_ID = "llm_openai"


def is_llm_synthesizer(synthesizer_id: str) -> bool:
    return synthesizer_id in LLM_OLLAMA_MODELS or synthesizer_id == LLM_OPENAI_SYNTHESIZER_ID


def llm_synthesizer_menu_ids() -> list[str]:
    """Synthesizer ids shown in the LSP/infoview menus (one entry per model)."""
    return [sid for sid in LLM_OLLAMA_MODELS if sid != "llm"] + [LLM_OPENAI_SYNTHESIZER_ID]


def llm_synthesizer_label(synthesizer_id: str) -> str:
    """Display label with the backend model visible in menus."""
    if synthesizer_id == LLM_OPENAI_SYNTHESIZER_ID:
        return "LLM generation (OpenAI-compatible)"
    model = LLM_OLLAMA_MODELS.get(synthesizer_id, synthesizer_id)
    return f"LLM generation ({model})"
