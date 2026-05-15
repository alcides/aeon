#!/usr/bin/env python3
"""Summarise a run.py CSV into a markdown report.

Usage:
    uv run python benchmarks/vericoding/summarize.py report.csv > REPORT.md
"""

from __future__ import annotations

import csv
import sys
from collections import Counter


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: summarize.py REPORT.csv", file=sys.stderr)
        return 2

    rows = list(csv.DictReader(open(sys.argv[1])))
    n = len(rows)
    statuses = Counter(r["status"] for r in rows)
    by_prefix: dict[str, Counter[str]] = {}
    for r in rows:
        prefix = r["id"][:2]
        bucket = by_prefix.setdefault(prefix, Counter())
        bucket[r["status"]] += 1

    pass_rate = 100.0 * statuses.get("pass", 0) / n if n else 0.0

    print("# Vericoding v1 — Aeon synthesis report")
    print()
    print(f"Tasks attempted: **{n}**")
    if rows:
        print(f"Synthesizer:     `{rows[0]['synthesizer']}`")
        # Reflect the budget used: every successful row's elapsed time is at
        # least the synthesis budget, so the floor of `min(elapsed)` is a
        # reasonable proxy. We report the median to absorb harness overhead.
        elapsed = sorted(float(r["elapsed"]) for r in rows if r["status"] in ("pass", "fail-synth"))
        if elapsed:
            median = elapsed[len(elapsed) // 2]
            print(f"Median per-task wall time: {median:.1f}s (budget + ~3s aeon startup)")
    print()
    print("## Overall")
    print()
    print("| status | count | % |")
    print("|---|---:|---:|")
    for s in ("pass", "fail-synth", "fail-parse", "rejected", "error"):
        count = statuses.get(s, 0)
        print(f"| {s} | {count} | {100.0 * count / n:.1f}% |")
    print()
    print(f"**Pass rate: {pass_rate:.1f}%**")
    print()

    print("## By source prefix")
    print()
    print("| prefix | total | pass | fail-synth | fail-parse |")
    print("|---|---:|---:|---:|---:|")
    for prefix in sorted(by_prefix):
        bucket = by_prefix[prefix]
        total = sum(bucket.values())
        print(
            f"| {prefix} | {total} | {bucket.get('pass', 0)} | "
            f"{bucket.get('fail-synth', 0)} | {bucket.get('fail-parse', 0)} |"
        )
    print()

    parse_fail = [r for r in rows if r["status"] == "fail-parse"]
    if parse_fail:
        print(f"## Parse/type failures ({len(parse_fail)})")
        print()
        print("| task | detail |")
        print("|---|---|")
        for r in parse_fail:
            detail = r["detail"].replace("|", "\\|")[:120]
            print(f"| `{r['id']}` | `{detail}` |")
        print()

    # Highlight degenerate-looking passes (division/modulo by zero / negative
    # division). Aeon's verifier doesn't constrain divisor-non-zero, so these
    # "pass" without actually computing anything meaningful.
    suspicious = [
        r for r in rows if r["status"] == "pass" and any(token in r["detail"] for token in ("% 0", "/ 0", "/ -"))
    ]
    if suspicious:
        print(f"## Degenerate passes ({len(suspicious)})")
        print()
        print(
            "These solutions are technically accepted by aeon's verifier but "
            "involve undefined arithmetic (`x % 0`, `x / 0`, `x / -1`). They are a "
            "known aeon SMT-completeness gap, not a translator issue."
        )
        print()
        print("| task | synthesized |")
        print("|---|---|")
        for r in suspicious:
            d = r["detail"].replace("|", "\\|")[:80]
            print(f"| `{r['id']}` | `{d}` |")
        print()

    return 0


if __name__ == "__main__":
    sys.exit(main())
