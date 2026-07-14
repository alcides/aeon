"""Tests for the OpenAI-compatible LLM client."""

from __future__ import annotations

import io
import json

import aeon.synthesis.modules.llm.openai_client as openai_client
import pytest


class _FakeHTTPResponse:
    def __init__(self, payload: dict):
        self._body = json.dumps(payload).encode()

    def read(self) -> bytes:
        return self._body

    def __enter__(self):
        return self

    def __exit__(self, *_args):
        return False


def test_generate_posts_chat_completion(monkeypatch):
    captured: dict = {}

    def fake_urlopen(request, timeout=120):
        captured["url"] = request.full_url
        captured["headers"] = dict(request.header_items())
        captured["payload"] = json.loads(request.data.decode())
        captured["timeout"] = timeout
        return _FakeHTTPResponse({"choices": [{"message": {"content": "42"}}]})

    monkeypatch.setenv("AEON_LLM_BASE_URL", "http://localhost:8080/v1")
    monkeypatch.setenv("AEON_LLM_API_KEY", "test-key")
    monkeypatch.setattr("urllib.request.urlopen", fake_urlopen)

    text = openai_client.generate("gpt-4o-mini", "hello", temperature=0.5)

    assert text == "42"
    assert captured["url"] == "http://localhost:8080/v1/chat/completions"
    assert captured["headers"]["Authorization"] == "Bearer test-key"
    assert captured["payload"] == {
        "model": "gpt-4o-mini",
        "messages": [{"role": "user", "content": "hello"}],
        "temperature": 0.5,
    }


def test_generate_uses_openai_api_key_fallback(monkeypatch):
    captured: dict = {}

    def fake_urlopen(request, timeout=120):
        captured["headers"] = dict(request.header_items())
        return _FakeHTTPResponse({"choices": [{"message": {"content": "ok"}}]})

    monkeypatch.delenv("AEON_LLM_API_KEY", raising=False)
    monkeypatch.setenv("OPENAI_API_KEY", "openai-key")
    monkeypatch.setattr("urllib.request.urlopen", fake_urlopen)

    openai_client.generate("gpt-4o-mini", "hello")

    assert captured["headers"]["Authorization"] == "Bearer openai-key"


def test_generate_raises_on_http_error(monkeypatch):
    import urllib.error

    def fake_urlopen(_request, timeout=120):
        raise urllib.error.HTTPError(
            url="http://localhost:8080/v1/chat/completions",
            code=401,
            msg="Unauthorized",
            hdrs=None,
            fp=io.BytesIO(b"invalid key"),
        )

    monkeypatch.setenv("AEON_LLM_BASE_URL", "http://localhost:8080/v1")
    monkeypatch.setattr("urllib.request.urlopen", fake_urlopen)

    with pytest.raises(RuntimeError, match="OpenAI-compatible API error \\(401\\)"):
        openai_client.generate("gpt-4o-mini", "hello")


def test_generate_raises_on_malformed_response(monkeypatch):
    def fake_urlopen(_request, timeout=120):
        return _FakeHTTPResponse({"unexpected": True})

    monkeypatch.setattr("urllib.request.urlopen", fake_urlopen)

    with pytest.raises(RuntimeError, match="Unexpected OpenAI-compatible API response"):
        openai_client.generate("gpt-4o-mini", "hello")
