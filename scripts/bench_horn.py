"""Compare Horn optimizations against a Git revision, using isolated processes.

Run from the repository root:
    .venv/bin/python scripts/bench_horn.py --baseline-ref HEAD \
        examples/syntax/maxI.ae examples/verification/horn_tournament.ae

Only fixpoint/weaken are loaded from the baseline; all other code is identical.
Each subprocess measures a cold compilation and then a warm compilation.
Imports and process startup are excluded. Programs are checked, never evaluated.
"""

from __future__ import annotations

import argparse
import ast
import json
import os
import platform
from pathlib import Path
from importlib.metadata import version
import statistics
import subprocess
import sys
import time
from typing import Any

ROOT = Path(__file__).resolve().parents[1]


def worker(path: str, variant: str, baseline_ref: str) -> None:
    sys.path.insert(0, str(ROOT))
    from loguru import logger
    from aeon.verification import horn, smt

    logger.remove()
    if variant == "before":
        source = subprocess.check_output(
            ["git", "show", f"{baseline_ref}:aeon/verification/horn.py"], cwd=ROOT, text=True
        )
        tree = ast.parse(source)
        tree.body = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name in {"fixpoint", "weaken"}]
        assert len(tree.body) == 2
        exec(compile(tree, "<baseline horn functions>", "exec"), horn.__dict__)

    metrics: dict[str, float | int] = {}
    from z3 import Solver

    original_solve, original_valid, original_check = horn.solve, horn.smt_valid, Solver.check
    original_weaken = horn.weaken

    def solve(*args, **kwargs):
        start = time.perf_counter()
        try:
            return original_solve(*args, **kwargs)
        finally:
            metrics["vc_seconds"] += time.perf_counter() - start

    def valid(c):
        metrics["smt_valid_calls"] += 1
        return original_valid(c)

    def check(self, *args, **kwargs):
        metrics["z3_checks"] += 1
        result = original_check(self, *args, **kwargs)
        if result == smt.unknown:
            metrics["unknown"] += 1
        return result

    def weaken(*args, **kwargs):
        metrics["weaken_calls"] += 1
        return original_weaken(*args, **kwargs)

    horn.solve, horn.smt_valid, horn.weaken, Solver.check = solve, valid, weaken, check
    # ``import aeon`` eagerly loads the facade: replace already-bound aliases
    # as well as the defining functions in this isolated benchmark process.
    for module_name, module in list(sys.modules.items()):
        if module_name.startswith("aeon."):
            if getattr(module, "solve", None) is original_solve:
                setattr(module, "solve", solve)
            if getattr(module, "smt_valid", None) is original_valid:
                setattr(module, "smt_valid", valid)
    from aeon.compilation.compile import compile_and_link
    from aeon.compilation.session import CompilationSession

    rows = []
    session = CompilationSession()
    for cache in ("cold", "warm"):
        metrics.update(vc_seconds=0.0, smt_valid_calls=0, z3_checks=0, unknown=0, weaken_calls=0)
        start = time.perf_counter()
        with session.activate():
            _unit, _core, _ctx, _metadata, _trusted, errors = compile_and_link(path, is_main_hole=False)
        rows.append(
            dict(metrics, cache=cache, compile_seconds=time.perf_counter() - start, errors=[str(e) for e in errors])
        )
        if errors:
            raise RuntimeError(rows[-1])
    print(json.dumps(rows))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="+")
    parser.add_argument("--baseline-ref", default="HEAD")
    parser.add_argument("--repeats", type=int, default=7)
    parser.add_argument("--worker", choices=["before", "after"], help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.worker:
        worker(args.paths[0], args.worker, args.baseline_ref)
        return
    if args.repeats < 1:
        parser.error("--repeats must be positive")
    baseline = subprocess.check_output(["git", "rev-parse", args.baseline_ref], cwd=ROOT, text=True).strip()
    samples: list[dict[str, Any]] = []
    for path in args.paths:
        for repetition in range(args.repeats):
            # Alternate order to reduce systematic bias from machine load.
            order = ("before", "after") if repetition % 2 == 0 else ("after", "before")
            for variant in order:
                output = subprocess.check_output(
                    [
                        sys.executable,
                        str(Path(__file__).resolve()),
                        "--worker",
                        variant,
                        "--baseline-ref",
                        baseline,
                        path,
                    ],
                    cwd=ROOT,
                    env={**os.environ, "PYTHONHASHSEED": "0"},
                    text=True,
                    timeout=120,
                )
                samples.extend(
                    dict(row, path=path, variant=variant, repetition=repetition) for row in json.loads(output)
                )
        print(f"Finished {path}", file=sys.stderr, flush=True)
    summary = []
    for path in args.paths:
        for cache in ("cold", "warm"):
            row: dict[str, Any] = dict(path=path, cache=cache)
            for variant in ("before", "after"):
                group = [s for s in samples if s["path"] == path and s["cache"] == cache and s["variant"] == variant]
                row[variant] = {
                    key: statistics.median(s[key] for s in group)
                    for key in (
                        "vc_seconds",
                        "compile_seconds",
                        "smt_valid_calls",
                        "z3_checks",
                        "weaken_calls",
                        "unknown",
                    )
                }
            row["vc_speedup"] = (
                row["before"]["vc_seconds"] / row["after"]["vc_seconds"] if row["after"]["vc_seconds"] else None
            )
            row["compile_speedup"] = row["before"]["compile_seconds"] / row["after"]["compile_seconds"]
            summary.append(row)
    print(
        json.dumps(
            dict(
                baseline=baseline,
                python=sys.version,
                platform=platform.platform(),
                z3=version("z3-solver"),
                repeats=args.repeats,
                summary=summary,
                samples=samples,
            ),
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
