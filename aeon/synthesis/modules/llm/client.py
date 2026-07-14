"""Unified LLM text generation for synthesis (Ollama or OpenAI-compatible)."""

from __future__ import annotations

import os

from ollama import generate as ollama_generate

from aeon.synthesis.modules.llm.openai_client import generate as openai_generate


def llm_provider() -> str:
    """Return ``ollama`` or ``openai`` for the active LLM backend."""
    explicit = os.environ.get("AEON_LLM_PROVIDER", "").strip().lower()
    if explicit in ("ollama", "openai"):
        return explicit
    if os.environ.get("AEON_LLM_BASE_URL") or os.environ.get("OPENAI_BASE_URL"):
        return "openai"
    return "ollama"


def default_openai_model() -> str:
    return os.environ.get("AEON_LLM_MODEL", "gpt-4o-mini")


def generate(*, model: str, prompt: str, temperature: float, provider: str | None = None) -> str:
    backend = provider or llm_provider()
    if backend == "openai":
        return openai_generate(model, prompt, temperature=temperature)
    result = ollama_generate(model=model, prompt=prompt, options={"temperature": temperature})
    return result.response
