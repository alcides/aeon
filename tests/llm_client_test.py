"""Tests for unified LLM client provider selection."""

from __future__ import annotations

import types

import aeon.synthesis.modules.llm.client as client


def test_llm_provider_defaults_to_ollama(monkeypatch):
    monkeypatch.delenv("AEON_LLM_PROVIDER", raising=False)
    monkeypatch.delenv("AEON_LLM_BASE_URL", raising=False)
    monkeypatch.delenv("OPENAI_BASE_URL", raising=False)
    assert client.llm_provider() == "ollama"


def test_llm_provider_honors_explicit_openai(monkeypatch):
    monkeypatch.setenv("AEON_LLM_PROVIDER", "openai")
    assert client.llm_provider() == "openai"


def test_llm_provider_infers_openai_from_base_url(monkeypatch):
    monkeypatch.delenv("AEON_LLM_PROVIDER", raising=False)
    monkeypatch.setenv("AEON_LLM_BASE_URL", "http://localhost:8080/v1")
    assert client.llm_provider() == "openai"


def test_generate_uses_openai_backend(monkeypatch):
    monkeypatch.setenv("AEON_LLM_PROVIDER", "openai")
    called = {}

    def fake_openai(model, prompt, *, temperature=0.0):
        called["model"] = model
        called["prompt"] = prompt
        called["temperature"] = temperature
        return "from-openai"

    monkeypatch.setattr(client, "openai_generate", fake_openai)
    monkeypatch.setattr(
        client,
        "ollama_generate",
        lambda **_kwargs: (_ for _ in ()).throw(AssertionError("should not call ollama")),
    )

    text = client.generate(model="gpt-4o-mini", prompt="hello", temperature=0.3)

    assert text == "from-openai"
    assert called == {"model": "gpt-4o-mini", "prompt": "hello", "temperature": 0.3}


def test_generate_uses_ollama_backend(monkeypatch):
    monkeypatch.setenv("AEON_LLM_PROVIDER", "ollama")

    def fake_ollama(**kwargs):
        return types.SimpleNamespace(response="from-ollama")

    monkeypatch.setattr(client, "ollama_generate", fake_ollama)
    monkeypatch.setattr(
        client,
        "openai_generate",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(AssertionError("should not call openai")),
    )

    text = client.generate(model="qwen2.5-coder:14b", prompt="hello", temperature=0.0)

    assert text == "from-ollama"
