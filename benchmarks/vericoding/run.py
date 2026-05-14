#!/usr/bin/env python3
"""Harness: translate Vericoding Dafny tasks to Aeon and run synthesis.

Fetches `.dfy` sources on demand from the upstream
Beneficial-AI-Foundation/vericoding-benchmark repo (raw.githubusercontent.com)
and caches them locally under `benchmarks/vericoding/.cache/`.

Usage
-----
    # Run a single task at a 30s synth budget with the default synthesizer.
    uv run python benchmarks/vericoding/run.py --task DD0080 --budget 30

    # Run the full v1 subset with a 60s budget per task, write CSV.
    uv run python benchmarks/vericoding/run.py --all --budget 60 --output report.csv

    # Translate only (no synthesis) so the .ae files can be inspected.
    uv run python benchmarks/vericoding/run.py --task DD0042 --translate-only

Exit code: 0 if every task succeeded or was a translation rejection;
1 if any task that translated did NOT synthesize a verified solution.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
import subprocess
import sys
import time
import urllib.request
from dataclasses import asdict, dataclass
from pathlib import Path

ROOT = Path(__file__).parent
CACHE_DIR = ROOT / ".cache"
TASK_LIST = ROOT / "v1_tasks.txt"
RAW_URL = "https://raw.githubusercontent.com/Beneficial-AI-Foundation/vericoding-benchmark/main/specs/{id}.dfy"

# Local import: the translator lives in the same directory, not a package.
sys.path.insert(0, str(ROOT))
from translate import TranslationError, translate  # noqa: E402

# Regex pulled from benchmark.py — extracts the synthesised hole text.
_HOLES_BLOCK = re.compile(r"^Synthesized holes:\s*$", re.MULTILINE)


@dataclass
class TaskResult:
    id: str
    status: str  # "pass", "fail-synth", "fail-parse", "rejected", "error"
    elapsed: float
    detail: str = ""  # short message: rejection reason, synthesized solution, error
    synthesizer: str = ""


def fetch_dafny(task_id: str) -> str:
    """Return the Dafny source for `task_id`, fetching and caching if needed."""
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    cached = CACHE_DIR / f"{task_id}.dfy"
    if cached.exists():
        return cached.read_text(errors="replace")
    url = RAW_URL.format(id=task_id)
    with urllib.request.urlopen(url, timeout=30) as resp:  # noqa: S310
        text = resp.read().decode("utf-8", errors="replace")
    cached.write_text(text)
    return text


def translate_to_file(task_id: str) -> Path:
    """Fetch + translate `task_id`, writing the .ae file to the cache. Returns the path."""
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    dafny = fetch_dafny(task_id)
    aeon = translate(dafny, task_id)
    out = CACHE_DIR / f"{task_id}.ae"
    out.write_text(aeon)
    return out


def run_aeon_synth(ae_file: Path, synthesizer: str, budget: int) -> tuple[bool, str, float]:
    """Invoke aeon synthesis. Returns (success, solution-or-error, elapsed)."""
    cmd = [
        "uv",
        "run",
        "python",
        "-m",
        "aeon",
        "-n",
        "-s",
        synthesizer,
        "--synthesis-format",
        "json",
        "--budget",
        str(budget),
        str(ae_file),
    ]
    t0 = time.perf_counter()
    try:
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=budget + 30,
        )
    except subprocess.TimeoutExpired:
        return False, "process-timeout", time.perf_counter() - t0
    elapsed = time.perf_counter() - t0

    stdout = proc.stdout or ""
    stderr = proc.stderr or ""

    # Look for the JSON-formatted holes block.
    m = _HOLES_BLOCK.search(stdout)
    if m is None:
        # Distinguish parse/type errors from synth timeouts.
        all_text = stdout + "\n" + stderr
        parse_markers = (
            ">>> Error",
            "Traceback",
            "Exception",
            "UnexpectedToken",
            "UnexpectedCharacters",
            "KeyError",
            "AssertionError",
            "Previous tokens:",
            "LiquidTypeCheckException",
        )
        if any(m in all_text for m in parse_markers):
            # For Python tracebacks, capture the LAST line (the exception type +
            # message) rather than the first "Traceback" header.
            lines = all_text.splitlines()
            err_line = ""
            for ln in reversed(lines):
                stripped = ln.strip()
                if not stripped:
                    continue
                if stripped.startswith((">>> Error", "AssertionError", "KeyError")):
                    err_line = stripped
                    break
                if (
                    "Exception" in stripped or "Error" in stripped or "LiquidTypeCheckException" in stripped
                ) and not stripped.startswith("Traceback"):
                    err_line = stripped
                    break
            if not err_line:
                # Fall back to a forward search.
                err_line = next(
                    (ln for ln in lines if any(m in ln for m in parse_markers)),
                    "",
                )
            return False, f"parse/type-error: {err_line[:200]}", elapsed
        snippet = (stderr.splitlines() or stdout.splitlines() or ["(no output)"])[-1]
        return False, f"no-synth-output: {snippet[:200]}", elapsed

    after = stdout[m.end() :].strip().splitlines()
    # Collect JSON lines until we hit a close brace at column 0.
    json_lines: list[str] = []
    for line in after:
        json_lines.append(line)
        if line.strip().startswith("}") and not line.startswith(" "):
            break
    try:
        holes = json.loads("\n".join(json_lines))
    except json.JSONDecodeError:
        return False, "json-decode-failed", elapsed

    if not isinstance(holes, dict) or not holes:
        return False, "no-holes-in-result", elapsed
    expr = next(iter(holes.values()))
    if not expr:
        return False, "empty-solution", elapsed
    return True, expr, elapsed


def run_task(task_id: str, synthesizer: str, budget: int, translate_only: bool) -> TaskResult:
    try:
        ae_file = translate_to_file(task_id)
    except TranslationError as e:
        return TaskResult(task_id, "rejected", 0.0, detail=str(e), synthesizer=synthesizer)
    except Exception as e:  # noqa: BLE001
        return TaskResult(task_id, "error", 0.0, detail=f"translator: {e}", synthesizer=synthesizer)

    if translate_only:
        return TaskResult(task_id, "translated", 0.0, detail=str(ae_file), synthesizer=synthesizer)

    ok, detail, elapsed = run_aeon_synth(ae_file, synthesizer, budget)
    if ok:
        status = "pass"
    elif detail.startswith("parse/type-error"):
        status = "fail-parse"
    else:
        status = "fail-synth"
    return TaskResult(task_id, status, elapsed, detail=detail, synthesizer=synthesizer)


def load_task_ids(arg: str | None) -> list[str]:
    if arg == "all" or arg is None:
        return [ln.strip() for ln in TASK_LIST.read_text().splitlines() if ln.strip()]
    return [arg]


def write_report(path: Path, results: list[TaskResult]) -> None:
    if path.suffix == ".csv":
        with path.open("w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=["id", "synthesizer", "status", "elapsed", "detail"])
            w.writeheader()
            for r in results:
                w.writerow(asdict(r))
    else:
        path.write_text(json.dumps([asdict(r) for r in results], indent=2))


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--task", help="Run a single task ID (e.g. DD0042_specs) instead of --all.")
    p.add_argument("--all", action="store_true", help="Run every task in v1_tasks.txt.")
    p.add_argument("--budget", type=int, default=30, help="Synthesis budget in seconds per task.")
    p.add_argument(
        "--synthesizer",
        default="tdsyn_enumerative",
        help="Aeon synthesizer name (gp / tdsyn_enumerative / tdsyn_random / enumerative / random_search / hc / 1p1 / smt).",
    )
    p.add_argument(
        "--translate-only",
        action="store_true",
        help="Translate to .ae and exit; skip synthesis.",
    )
    p.add_argument(
        "--output",
        type=Path,
        default=None,
        help="Write a report file (.csv or .json). If omitted, only stdout is produced.",
    )
    p.add_argument(
        "--limit",
        type=int,
        default=None,
        help="With --all, run only the first N tasks (useful for smoke tests).",
    )
    args = p.parse_args()

    if args.task and args.all:
        p.error("--task and --all are mutually exclusive")
    if not (args.task or args.all):
        p.error("must pass --task ID or --all")
    task_ids = load_task_ids(args.task if args.task else "all")
    if args.limit is not None:
        task_ids = task_ids[: args.limit]

    results: list[TaskResult] = []
    for tid in task_ids:
        sys.stdout.write(f"[{tid}] ... ")
        sys.stdout.flush()
        r = run_task(tid, args.synthesizer, args.budget, args.translate_only)
        results.append(r)
        sys.stdout.write(f"{r.status:12s}  {r.elapsed:6.2f}s  {r.detail[:80]}\n")

    n_pass = sum(1 for r in results if r.status == "pass")
    n_synth = sum(1 for r in results if r.status == "fail-synth")
    n_parse = sum(1 for r in results if r.status == "fail-parse")
    n_rej = sum(1 for r in results if r.status == "rejected")
    n_err = sum(1 for r in results if r.status == "error")
    print()
    print(f"Pass:        {n_pass}/{len(results)}")
    print(f"Fail-synth:  {n_synth}")
    print(f"Fail-parse:  {n_parse}")
    print(f"Rejected:    {n_rej}")
    print(f"Error:       {n_err}")

    if args.output:
        write_report(args.output, results)
        print(f"Wrote {args.output}")

    return 0 if n_err == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
