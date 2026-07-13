"""Tests for automated Ollama model pull and memory release."""

from __future__ import annotations

import types

import aeon.synthesis.modules.llm.ollama_manager as mgr
import pytest


def _running(name: str, vram: int):
    return types.SimpleNamespace(model=name, name=name, size_vram=vram)


def test_pull_skips_when_model_installed(monkeypatch):
    monkeypatch.setattr(mgr, "_auto_pull_enabled", lambda: True)
    monkeypatch.setattr(mgr, "_installed_model_names", lambda: {"qwen2.5-coder:14b"})
    called = {"pull": False}

    def fake_pull(model, stream=False):
        called["pull"] = True
        return iter([])

    monkeypatch.setattr(mgr.ollama, "pull", fake_pull)
    mgr.pull_model("qwen2.5-coder:14b")
    assert called["pull"] is False


def test_pull_downloads_missing_model(monkeypatch):
    monkeypatch.setattr(mgr, "_auto_pull_enabled", lambda: True)
    monkeypatch.setattr(mgr, "_installed_model_names", lambda: set())

    def fake_pull(model, stream=False):
        assert model == "deepseek-coder:6.7b"
        assert stream is True
        yield types.SimpleNamespace(status="pulling manifest")
        yield types.SimpleNamespace(status="downloading", completed=50, total=100)

    monkeypatch.setattr(mgr.ollama, "pull", fake_pull)
    mgr.pull_model("deepseek-coder:6.7b")


def test_pull_disabled_raises_when_missing(monkeypatch):
    monkeypatch.setattr(mgr, "_auto_pull_enabled", lambda: False)
    monkeypatch.setattr(mgr, "_installed_model_names", lambda: set())
    with pytest.raises(RuntimeError, match="AEON_OLLAMA_AUTO_PULL"):
        mgr.pull_model("codellama:13b")


def test_free_memory_unloads_other_running_models(monkeypatch):
    monkeypatch.setattr(
        mgr,
        "_running_models",
        lambda: [
            _running("qwen2.5-coder:32b", 20 * 1024**3),
            _running("codellama:13b", 8 * 1024**3),
        ],
    )
    unloaded: list[str] = []
    monkeypatch.setattr(mgr, "_unload_model", unloaded.append)

    mgr.free_memory_for("qwen2.5-coder:14b", budget_bytes=56 * 1024**3)

    assert unloaded == ["qwen2.5-coder:32b", "codellama:13b"]


def test_free_memory_unloads_target_when_over_budget(monkeypatch):
    monkeypatch.setattr(
        mgr,
        "_running_models",
        lambda: [_running("qwen2.5-coder:32b", 40 * 1024**3)],
    )
    unloaded: list[str] = []
    monkeypatch.setattr(mgr, "_unload_model", unloaded.append)

    mgr.free_memory_for("qwen2.5-coder:32b", budget_bytes=20 * 1024**3)

    assert unloaded == ["qwen2.5-coder:32b"]


def test_release_unloads_when_enabled(monkeypatch):
    monkeypatch.setattr(mgr, "_release_after_enabled", lambda: True)
    monkeypatch.setattr(mgr, "_running_models", lambda: [_running("qwen2.5-coder:14b", 10 * 1024**3)])
    unloaded: list[str] = []
    monkeypatch.setattr(mgr, "_unload_model", unloaded.append)

    mgr.release_ollama_model("qwen2.5-coder:14b")

    assert unloaded == ["qwen2.5-coder:14b"]


def test_release_noop_when_disabled(monkeypatch):
    monkeypatch.setattr(mgr, "_release_after_enabled", lambda: False)
    monkeypatch.setattr(mgr, "_running_models", lambda: [_running("qwen2.5-coder:14b", 10 * 1024**3)])
    monkeypatch.setattr(
        mgr,
        "_unload_model",
        lambda _model: (_ for _ in ()).throw(AssertionError("should not unload")),
    )
    mgr.release_ollama_model("qwen2.5-coder:14b")


def test_installed_model_names_when_name_attr_missing(monkeypatch):
    """ollama-python list entries expose ``model`` but not ``name``."""
    entry = types.SimpleNamespace(model="qwen2.5-coder:14b")
    monkeypatch.setattr(mgr.ollama, "list", lambda: types.SimpleNamespace(models=[entry]))
    assert mgr.is_model_installed("qwen2.5-coder:14b")


def test_running_models_when_name_attr_missing(monkeypatch):
    entry = types.SimpleNamespace(model="codellama:13b", size_vram=8 * 1024**3)
    monkeypatch.setattr(mgr.ollama, "ps", lambda: types.SimpleNamespace(models=[entry]))
    assert mgr._running_models() == [mgr.RunningModel(name="codellama:13b", size_vram=8 * 1024**3)]
