"""Record compilation-only timings and environment, without executing programs."""

from __future__ import annotations

import argparse
from importlib.metadata import version
import json
import os
import platform
import statistics
import sys
import time

from loguru import logger

from aeon.compilation.compile import compile_and_link


def measure(path: str, repeats: int) -> dict:
    durations: list[float] = []
    for _ in range(repeats):
        start = time.perf_counter()
        unit, _core, _context, _metadata, _trusted, errors = compile_and_link(path, is_main_hole=False)
        durations.append(time.perf_counter() - start)
        if errors:
            raise RuntimeError(f"{path}: " + "; ".join(str(error) for error in errors))
    return {
        "path": path,
        "source_hash": unit.source_hash,
        "seconds": durations,
        "median_seconds": statistics.median(durations),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="+")
    parser.add_argument("--repeats", type=int, default=3)
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("--repeats must be positive")
    logger.remove()
    report = {
        "compiler": version("AeonLang"),
        "revision": os.environ.get("GITHUB_SHA", "working-tree"),
        "python": sys.version,
        "platform": platform.platform(),
        "z3": version("z3-solver"),
        "scope": "compile-only, independent sessions, existing disk caches allowed",
        "repeats": args.repeats,
        "results": [measure(path, args.repeats) for path in args.paths],
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
