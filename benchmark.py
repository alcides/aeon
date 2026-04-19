#!/usr/bin/env python3
"""Aeon synthesizer benchmark.

Runs every example in examples/benchmarks/ against each synthesizer and
reports success (hole filled), wall-clock time, best fitness, and the
synthesised expression.

Usage
-----
    uv run python benchmark.py                        # all synthesizers, 3-min budget
    uv run python benchmark.py --budget 60            # 60-second budget per run
    uv run python benchmark.py --synthesizers tdsyn_enumerative gp   # pick synthesizers
    uv run python benchmark.py --examples "examples/benchmarks/bench_int*.ae"
    uv run python benchmark.py --output json          # machine-readable output
    uv run python benchmark.py --output csv           # spreadsheet-friendly output

Exit code is 0 when every run succeeds, 1 otherwise.
"""

from __future__ import annotations

import argparse
import csv
import glob
import json
import re
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

ROOT = Path(__file__).parent
EXAMPLES_DIR = ROOT / "examples" / "benchmarks"

DEFAULT_SYNTHESIZERS = ["tdsyn_enumerative", "tdsyn", "gp", "random_search", "enumerative", "hc", "1p1"]
DEFAULT_BUDGET = 180  # seconds (3 minutes)

# Matches the TerminalUI progress lines:
# "Target: x (12.3 / 180.0s) | Best: <expr> ([0.0]) | Current: ..."
_BEST_QUALITY_RE = re.compile(r"\| Best: .+? \((\[.*?\])\) \| Current:")


@dataclass
class Result:
    example: str
    synthesizer: str
    success: bool
    elapsed: float
    quality: Optional[str] = None  # best fitness string, e.g. "[0.0]"
    solution: Optional[str] = None  # pretty-printed synthesised expression
    error: Optional[str] = None


def _extract_quality(stdout: str) -> Optional[str]:
    """Return the last best-fitness string seen in TerminalUI progress output."""
    matches = _BEST_QUALITY_RE.findall(stdout)
    return matches[-1] if matches else None


def _extract_solution(stdout: str) -> Optional[str]:
    """
    Parse the JSON block emitted by --synthesis-format json.

    The output contains a section like:
        Synthesized holes:
        {
          "?holeName": "expression"
        }
    Returns the first non-empty hole value, or None if synthesis failed.
    """
    in_block = False
    json_lines: list[str] = []
    for line in stdout.splitlines():
        if line.strip() == "Synthesized holes:":
            in_block = True
            continue
        if in_block:
            json_lines.append(line)
            # A standalone "}" closes the top-level object.
            if line.strip() == "}":
                break

    if not json_lines:
        return None

    try:
        data: dict = json.loads("\n".join(json_lines))
    except json.JSONDecodeError:
        return None

    for value in data.values():
        if isinstance(value, str) and value != "None":
            return value
    return None


def run_one(example: Path, synthesizer: str, budget: int) -> Result:
    """Run synthesis for *example* with *synthesizer* and return a Result."""
    cmd = [
        "uv",
        "run",
        "python",
        "-m",
        "aeon",
        "--no-main",
        "--budget",
        str(budget),
        "-s",
        synthesizer,
        "--synthesis-format",
        "json",
        str(example),
    ]
    t0 = time.monotonic()
    try:
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=budget + 90,  # generous extra buffer beyond the synthesis budget
        )
        elapsed = time.monotonic() - t0

        combined = proc.stdout + "\n" + proc.stderr
        quality = _extract_quality(combined)
        solution = _extract_solution(proc.stdout)
        success = solution is not None

        error: Optional[str] = None
        if proc.returncode != 0 and not success:
            raw = (proc.stderr or proc.stdout or "non-zero exit").strip()
            error = raw[-300:] if len(raw) > 300 else raw

        return Result(
            example=example.name,
            synthesizer=synthesizer,
            success=success,
            elapsed=elapsed,
            quality=quality,
            solution=solution,
            error=error,
        )
    except subprocess.TimeoutExpired:
        return Result(
            example=example.name,
            synthesizer=synthesizer,
            success=False,
            elapsed=time.monotonic() - t0,
            error="hard timeout",
        )
    except Exception as exc:
        return Result(
            example=example.name,
            synthesizer=synthesizer,
            success=False,
            elapsed=time.monotonic() - t0,
            error=str(exc),
        )


# ── Pretty table ──────────────────────────────────────────────────────────────


def _cell(r: Result) -> str:
    if r.success:
        q = f" q={r.quality}" if r.quality else ""
        return f"✓ {r.elapsed:.1f}s{q}"
    if r.error == "hard timeout":
        return "TIMEOUT"
    return f"✗ {r.elapsed:.1f}s"


def _print_table(results: list[Result], synthesizers: list[str]) -> None:
    examples = list(dict.fromkeys(r.example for r in results))
    by_key = {(r.example, r.synthesizer): r for r in results}

    name_w = max(len(e) for e in examples) + 2
    # cell width: at least synthesizer name + 2, but wide enough for timing+quality
    sample_cells = [_cell(r) for r in results]
    col_w = max(max((len(c) for c in sample_cells), default=12), max(len(s) for s in synthesizers)) + 3

    sep = "─" * (name_w + col_w * len(synthesizers))
    header = f"{'Example':<{name_w}}" + "".join(f"{s:^{col_w}}" for s in synthesizers)
    print(sep)
    print(header)
    print(sep)

    for ex in examples:
        row = f"{ex:<{name_w}}"
        for syn in synthesizers:
            r = by_key.get((ex, syn))
            cell = _cell(r) if r else "?"
            row += f"{cell:^{col_w}}"
        print(row)

    print(sep)

    # Summary row
    summary = f"{'Success rate':<{name_w}}"
    for syn in synthesizers:
        wins = sum(1 for ex in examples if by_key.get((ex, syn), Result("", "", False, 0)).success)
        cell = f"{wins}/{len(examples)}"
        summary += f"{cell:^{col_w}}"
    print(summary)
    print(sep)


# ── Entry point ───────────────────────────────────────────────────────────────


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compare Aeon synthesizers across benchmark examples.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument(
        "--budget",
        type=int,
        default=DEFAULT_BUDGET,
        metavar="SECONDS",
        help=f"Synthesis time budget per run (default: {DEFAULT_BUDGET}s = 3 min)",
    )
    parser.add_argument(
        "--synthesizers",
        nargs="+",
        default=DEFAULT_SYNTHESIZERS,
        metavar="NAME",
        help="Synthesizers to compare (default: tdsyn_enumerative tdsyn gp random_search enumerative hc 1p1)",
    )
    parser.add_argument(
        "--examples",
        default=str(EXAMPLES_DIR / "*.ae"),
        metavar="GLOB",
        help=f"Glob for benchmark files (default: {EXAMPLES_DIR / '*.ae'})",
    )
    parser.add_argument(
        "--output",
        choices=["table", "json", "csv"],
        default="table",
        help="Output format (default: table)",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()

    example_files = sorted(Path(p) for p in glob.glob(args.examples))
    if not example_files:
        print(f"No examples found for pattern: {args.examples}", file=sys.stderr)
        return 1

    total = len(example_files) * len(args.synthesizers)
    print(
        f"Running {len(example_files)} examples × {len(args.synthesizers)} synthesizers"
        f" = {total} runs  (budget: {args.budget}s each)\n",
        flush=True,
    )

    results: list[Result] = []
    pairs = [(ex, syn) for ex in example_files for syn in args.synthesizers]
    for n, (ex, syn) in enumerate(pairs, start=1):
        label = f"[{n:>{len(str(total))}}/{total}]  {ex.name:<42} × {syn:<14}"
        print(label, end=" ... ", flush=True)
        r = run_one(ex, syn, args.budget)
        results.append(r)
        print(_cell(r), flush=True)

    print()

    if args.output == "table":
        _print_table(results, args.synthesizers)

    elif args.output == "json":
        print(
            json.dumps(
                [
                    {
                        "example": r.example,
                        "synthesizer": r.synthesizer,
                        "success": r.success,
                        "elapsed_s": round(r.elapsed, 3),
                        "quality": r.quality,
                        "solution": r.solution,
                        "error": r.error,
                    }
                    for r in results
                ],
                indent=2,
            )
        )

    elif args.output == "csv":
        writer = csv.writer(sys.stdout)
        writer.writerow(["example", "synthesizer", "success", "elapsed_s", "quality", "solution", "error"])
        for r in results:
            writer.writerow(
                [
                    r.example,
                    r.synthesizer,
                    r.success,
                    round(r.elapsed, 3),
                    r.quality or "",
                    r.solution or "",
                    r.error or "",
                ]
            )

    all_ok = all(r.success for r in results)
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
