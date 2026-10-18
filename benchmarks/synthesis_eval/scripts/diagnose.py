#!/usr/bin/env python3
"""Triage full-suite results using Aeon's exit categories and raw logs."""

import argparse
from collections import Counter
import csv
import gzip
import importlib.util
import json
from pathlib import Path

EXIT_CATEGORIES = {
    3: "syntax_error",
    4: "aeon_import_error",
    5: "type_mismatch",
    6: "unification_error",
    7: "kind_mismatch",
    8: "unknown_name",
    9: "method_resolution_error",
    10: "missing_instance",
    11: "non_orderable_comparison",
    12: "linearity_error",
    13: "core_type_error",
    14: "invalid_refinement",
    15: "undecidable_refinement",
    16: "other_compile_error",
}


def log_path(path):
    return path if path.exists() else Path(str(path) + ".gz")


def read_log(path):
    actual = log_path(path)
    if actual.suffix == ".gz":
        with gzip.open(actual, "rt", errors="replace") as stream:
            return stream.read()
    return actual.read_text(errors="replace")


def is_unsupported_goal(text):
    root = Path(__file__).resolve().parents[1]
    current_file = root / "source/current.json"
    current = json.loads(current_file.read_text()) if current_file.exists() else {"path": "source/aeon"}
    candidates = [
        root / current["path"] / "aeon/benchmarks/outcomes.py",
        root / "aeon-psb2-github/aeon/benchmarks/outcomes.py",
        root.parents[1] / "aeon/benchmarks/outcomes.py",
    ]
    for candidate in candidates:
        if candidate.exists():
            spec = importlib.util.spec_from_file_location("_evaluation_outcomes", candidate)
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            return module.unsupported_goal(text)
    return "cannot handle hole" in text or "requires at least one @minimize" in text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", required=True)
    args = parser.parse_args()
    run = Path(args.run)
    plan = json.loads((run / "plan.json").read_text())
    rows = []
    for path in sorted((run / "results").glob("*.json")):
        result = json.loads(path.read_text())
        stdout = read_log(path.with_suffix(".stdout"))
        stderr = read_log(path.with_suffix(".stderr"))
        combined = stdout + "\n" + stderr
        status = result["status"]
        category = EXIT_CATEGORIES.get(result["exit_code"], status)
        if status == "timeout":
            category = "timeout_during_search" if "# Synthesizing" in stdout else "timeout_before_search"
        elif status == "error" and result["exit_code"] == 1:
            category = "unhandled_exception"
        if status != "timeout" and is_unsupported_goal(combined):
            category = "unsupported_goal"
        if status != "timeout" and ("ModuleNotFoundError" in combined or "requires the optional" in combined):
            category = "python_dependency_missing"
        if status != "timeout" and ("FileNotFoundError" in combined):
            category = "external_file_missing"
        if "No holes to synthesize." in combined:
            category = "no_compiler_holes"
        significant = [
            line.strip()
            for line in combined.splitlines()
            if line.strip().startswith(
                (
                    ">>>",
                    "aeon.",
                    "AssertionError",
                    "FileNotFoundError",
                    "ModuleNotFoundError",
                    "TypeError",
                    "ValueError",
                    "NotImplementedError",
                    "NameError",
                    "RecursionError",
                    "RuntimeError",
                )
            )
        ]
        rows.append(
            {
                "id": result["id"],
                "case": result["case"],
                "category": category,
                "status": status,
                "exit_code": result["exit_code"],
                "elapsed_s": round(result["elapsed_s"], 3),
                "search_started": "# Synthesizing" in stdout,
                "detail": " | ".join(significant[-3:])[:1500],
                "stdout": str(log_path(path.with_suffix(".stdout"))),
                "stderr": str(log_path(path.with_suffix(".stderr"))),
            }
        )
    for name, values in [
        ("triage.csv", rows),
        ("problems.csv", [x for x in rows if x["category"] not in ("filled", "no_solution")]),
    ]:
        with (run / name).open("w") as f:
            writer = csv.DictWriter(f, fieldnames=list(rows[0]) if rows else ["id", "case", "category"])
            writer.writeheader()
            writer.writerows(values)
    counts = Counter(x["category"] for x in rows)
    lines = [f"Completed {len(rows)}/{len(plan['jobs'])} trials.", "", "| Category | Programs |", "|---|---:|"]
    lines.extend(f"| {category} | {count} |" for category, count in counts.most_common())
    lines += [
        "",
        "Timeouts are observations under this run’s deadline, not evidence of invalid programs. Incomplete means the CLI returned without filling every expected named hole. Compiler errors and unhandled exceptions require inspecting their saved logs.",
        "",
        "See triage.csv for every trial and problems.csv for cases to inspect. Missing results are reported separately by eval.py collect.",
    ]
    (run / "diagnosis.md").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
