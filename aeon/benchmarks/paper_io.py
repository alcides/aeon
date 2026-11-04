"""Score contest programs against downloaded, checksum-pinned I/O fixtures."""

from __future__ import annotations

import gzip
import hashlib
import json
from functools import lru_cache
from pathlib import Path
from typing import Callable

DATA_ROOT = Path(__file__).resolve().parents[2] / "examples/benchmarks/asac/data"


@lru_cache(maxsize=4)
def load_cases(task: str, checksum: str) -> tuple[tuple[str, str], ...]:
    if Path(task).name != task:
        raise ValueError("Expected a dataset task name, not a path")
    path = DATA_ROOT / (task + ".json.gz")
    if not path.exists():
        raise FileNotFoundError(
            f"Missing {path}. Run python -m scripts.paper_benchmarks --sources <artifact-directory> --suite asac"
        )
    payload = gzip.decompress(path.read_bytes())
    if hashlib.sha256(payload).hexdigest() != checksum:
        raise ValueError(f"Dataset checksum mismatch: {path}")
    cases = json.loads(payload)
    if (
        not isinstance(cases, list)
        or not cases
        or any(not isinstance(x, list) or len(x) != 2 or not all(isinstance(s, str) for s in x) for x in cases)
    ):
        raise ValueError(f"Invalid I/O corpus: {path}")
    return tuple((x, y) for x, y in cases)


def failures(task: str, checksum: str, candidate: Callable[[str], str]) -> int:
    # Dataset errors must be visible rather than masquerading as a bad program.
    cases = load_cases(task, checksum)
    failed = 0
    for source, expected in cases:
        try:
            actual = candidate(source)
            passed = isinstance(actual, str) and actual.split() == expected.split()
        except (ArithmeticError, ValueError, IndexError, KeyError, TypeError, RecursionError):
            passed = False
        failed += not passed
    return failed
