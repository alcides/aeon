"""Ollama model lifecycle: pull on demand and free unified memory before/after synthesis."""

from __future__ import annotations

import json
import os
import subprocess
import urllib.error
import urllib.request
from dataclasses import dataclass

import ollama
from loguru import logger

# Approximate peak RAM when a model is loaded (weights + modest context) on Apple
# Silicon. Used only for eviction heuristics — actual use is reported by ``ps()``.
OLLAMA_MODEL_VRAM_GB: dict[str, float] = {
    "qwen2.5-coder:32b": 22.0,
    "qwen2.5-coder:14b": 11.0,
    "deepseek-coder-v2:16b": 12.0,
    "codellama:13b": 10.0,
    "starcoder2:15b": 11.0,
    "deepseek-coder:6.7b": 6.0,
}


def _ollama_base_url() -> str:
    host = os.environ.get("OLLAMA_HOST", "http://127.0.0.1:11434")
    if not host.startswith("http"):
        host = f"http://{host}"
    return host.rstrip("/")


def _memory_budget_bytes() -> int:
    gb = float(os.environ.get("AEON_OLLAMA_MEMORY_BUDGET_GB", "56"))
    return int(gb * 1024**3)


def _auto_pull_enabled() -> bool:
    return os.environ.get("AEON_OLLAMA_AUTO_PULL", "1").lower() not in ("0", "false", "no")


def _release_after_enabled() -> bool:
    return os.environ.get("AEON_OLLAMA_RELEASE_AFTER", "1").lower() not in ("0", "false", "no")


@dataclass(frozen=True)
class RunningModel:
    name: str
    size_vram: int


def _installed_model_names() -> set[str]:
    names: set[str] = set()
    for entry in ollama.list().models:
        names.add(entry.model)
        if entry.name:
            names.add(entry.name)
    return names


def is_model_installed(model: str) -> bool:
    return model in _installed_model_names()


def _estimate_vram_bytes(model: str) -> int:
    gb = OLLAMA_MODEL_VRAM_GB.get(model, 12.0)
    return int(gb * 1024**3)


def _running_models() -> list[RunningModel]:
    try:
        response = ollama.ps()
    except Exception as exc:
        logger.warning("Could not list running Ollama models: {}", exc)
        return []
    running: list[RunningModel] = []
    for entry in response.models:
        name = entry.model or entry.name
        if not name:
            continue
        running.append(RunningModel(name=name, size_vram=int(getattr(entry, "size_vram", 0) or 0)))
    return running


def _unload_model(model: str) -> None:
    """Unload ``model`` from RAM (keeps the weights on disk)."""
    base = _ollama_base_url()
    payload = json.dumps({"model": model, "prompt": "", "keep_alive": 0}).encode()
    request = urllib.request.Request(
        f"{base}/api/generate",
        data=payload,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=60) as response:
            response.read()
        return
    except urllib.error.URLError as exc:
        logger.debug("HTTP unload failed for {} ({}); trying ``ollama stop``", model, exc)

    try:
        subprocess.run(
            ["ollama", "stop", model],
            check=False,
            capture_output=True,
            text=True,
            timeout=60,
        )
    except (FileNotFoundError, subprocess.TimeoutExpired) as exc:
        logger.warning("Could not unload Ollama model {}: {}", model, exc)


def pull_model(model: str) -> None:
    """Download ``model`` if it is not already present locally."""
    if not _auto_pull_enabled():
        if not is_model_installed(model):
            raise RuntimeError(
                f"Ollama model {model!r} is not installed and AEON_OLLAMA_AUTO_PULL is disabled. "
                f"Run: ollama pull {model}"
            )
        return

    if is_model_installed(model):
        return

    logger.info("Pulling Ollama model {} …", model)
    for progress in ollama.pull(model, stream=True):
        status = getattr(progress, "status", None)
        if status:
            completed = getattr(progress, "completed", None)
            total = getattr(progress, "total", None)
            if completed is not None and total:
                pct = 100.0 * completed / total
                logger.info("{} ({:.0f}%)", status, pct)
            else:
                logger.info("{}", status)


def free_memory_for(model: str, budget_bytes: int | None = None) -> None:
    """Unload loaded Ollama models until ``model`` fits in the memory budget."""
    budget = budget_bytes if budget_bytes is not None else _memory_budget_bytes()
    needed = _estimate_vram_bytes(model)

    running = _running_models()
    if not running:
        if needed > budget:
            logger.warning(
                "Model {} may need ~{:.0f} GB but AEON_OLLAMA_MEMORY_BUDGET_GB is {:.0f}. "
                "Consider a smaller ``llm_*`` backend.",
                model,
                needed / 1024**3,
                budget / 1024**3,
            )
        return

    loaded_other = [m for m in running if m.name != model]
    for entry in loaded_other:
        logger.info("Unloading Ollama model {} to free memory", entry.name)
        _unload_model(entry.name)

    running = _running_models()
    loaded_bytes = sum(m.size_vram for m in running if m.name != model)
    target_loaded = next((m.size_vram for m in running if m.name == model), 0)
    projected = max(target_loaded, needed) if not any(m.name == model for m in running) else target_loaded

    if loaded_bytes + projected > budget:
        for entry in running:
            if entry.name == model:
                logger.info("Unloading {} before reload to stay within memory budget", model)
            else:
                logger.info("Unloading Ollama model {} (memory budget)", entry.name)
            _unload_model(entry.name)


def prepare_ollama_model(model: str) -> None:
    """Ensure ``model`` is on disk and enough unified memory is available."""
    pull_model(model)
    free_memory_for(model)


def release_ollama_model(model: str) -> None:
    """Unload ``model`` from RAM after synthesis (garbage-collection style)."""
    if not _release_after_enabled():
        return
    if any(m.name == model for m in _running_models()):
        logger.debug("Releasing Ollama model {} from memory", model)
        _unload_model(model)
