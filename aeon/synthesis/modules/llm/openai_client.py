"""OpenAI-compatible ``/v1/chat/completions`` client for LLM synthesis."""

from __future__ import annotations

import json
import os
import urllib.error
import urllib.request


def openai_base_url() -> str:
    url = os.environ.get("AEON_LLM_BASE_URL") or os.environ.get("OPENAI_BASE_URL", "https://api.openai.com/v1")
    return url.rstrip("/")


def openai_api_key() -> str | None:
    return os.environ.get("AEON_LLM_API_KEY") or os.environ.get("OPENAI_API_KEY")


def _timeout_seconds() -> float:
    return float(os.environ.get("AEON_LLM_TIMEOUT", "120"))


def generate(model: str, prompt: str, *, temperature: float = 0.0) -> str:
    """Generate text from an OpenAI-compatible chat/completions endpoint."""
    payload = {
        "model": model,
        "messages": [{"role": "user", "content": prompt}],
        "temperature": temperature,
    }
    headers = {"Content-Type": "application/json"}
    api_key = openai_api_key()
    if api_key:
        headers["Authorization"] = f"Bearer {api_key}"

    request = urllib.request.Request(
        f"{openai_base_url()}/chat/completions",
        data=json.dumps(payload).encode(),
        headers=headers,
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=_timeout_seconds()) as response:
            body = json.loads(response.read())
    except urllib.error.HTTPError as exc:
        err_body = exc.read().decode(errors="replace")
        raise RuntimeError(f"OpenAI-compatible API error ({exc.code}): {err_body}") from exc
    except urllib.error.URLError as exc:
        raise RuntimeError(f"Could not reach OpenAI-compatible API at {openai_base_url()}: {exc}") from exc

    try:
        content = body["choices"][0]["message"]["content"]
    except (KeyError, IndexError, TypeError) as exc:
        raise RuntimeError(f"Unexpected OpenAI-compatible API response: {body!r}") from exc
    if not isinstance(content, str):
        raise RuntimeError(f"Unexpected OpenAI-compatible API response: {body!r}")
    return content
