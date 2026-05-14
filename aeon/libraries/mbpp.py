"""Runtime helpers for the MBPP benchmark.

Used by ``libraries/MBPP.ae`` to load the sanitized MBPP dataset and to score
synthesis candidates against each problem's ``test_list`` of Python assertions.
"""

from __future__ import annotations

import json
import math
import re
from pathlib import Path
from typing import Any, Callable

DEFAULT_DATA_PATH = "libraries/data/mbpp.json"


def load(path: str | None = None) -> list[dict[str, Any]]:
    """Load the sanitized MBPP dataset from ``path``.

    If no path is given, falls back to ``libraries/data/mbpp.json`` relative to
    the current working directory.
    """
    candidate = Path(path) if path else Path(DEFAULT_DATA_PATH)
    return json.loads(candidate.read_text())


def get_task(dataset: list[dict[str, Any]], task_id: int) -> dict[str, Any]:
    """Return the problem dict with the given ``task_id``."""
    for problem in dataset:
        if problem["task_id"] == task_id:
            return problem
    raise KeyError(f"MBPP task_id {task_id} not found in dataset")


def _extract_func_name(problem: dict[str, Any]) -> str:
    match = re.search(r"def\s+(\w+)\s*\(", problem["code"])
    if match is None:
        raise ValueError(f"Cannot extract function name from MBPP problem {problem.get('task_id')}")
    return match.group(1)


def _build_env(problem: dict[str, Any], func_name: str, fn: Callable[..., Any]) -> dict[str, Any]:
    env: dict[str, Any] = {"math": math, func_name: fn}
    for imp in problem.get("test_imports", []) or []:
        exec(imp, env)
    return env


def evaluate(problem: dict[str, Any], fn: Callable[..., Any]) -> list[float]:
    """Run each assertion in ``problem['test_list']`` against ``fn``.

    Returns a list with one float per assertion: ``0.0`` if the assertion
    passes, ``1.0`` otherwise. The synthesizer uses this as a multi-objective
    fitness vector — the all-zero vector is the optimum.
    """
    func_name = _extract_func_name(problem)
    env = _build_env(problem, func_name, fn)
    errors: list[float] = []
    for assertion in problem["test_list"]:
        try:
            exec(assertion, env)
            errors.append(0.0)
        except Exception:
            errors.append(1.0)
    return errors


def evaluate_arity_1(problem: dict[str, Any], fn: Callable[[Any], Any]) -> list[float]:
    """Score an Aeon arity-1 candidate (curried as ``fn(x)``)."""
    return evaluate(problem, lambda a: fn(a))


def evaluate_arity_2(problem: dict[str, Any], fn: Callable[[Any], Callable[[Any], Any]]) -> list[float]:
    """Score an Aeon arity-2 candidate (curried as ``fn(x)(y)``)."""
    return evaluate(problem, lambda a, b: fn(a)(b))


def evaluate_arity_3(
    problem: dict[str, Any],
    fn: Callable[[Any], Callable[[Any], Callable[[Any], Any]]],
) -> list[float]:
    """Score an Aeon arity-3 candidate (curried as ``fn(x)(y)(z)``)."""
    return evaluate(problem, lambda a, b, c: fn(a)(b)(c))


def test_count(problem: dict[str, Any]) -> int:
    """Number of assertions in the problem's ``test_list``."""
    return len(problem["test_list"])
