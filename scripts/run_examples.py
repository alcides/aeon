"""Recursively validate examples in isolated, bounded CLI processes.

Synthesis benchmarks are typechecked, never solved. Each example belongs to
exactly one deterministic shard; newly added .ae files are discovered automatically.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent


@dataclass(frozen=True)
class Example:
    path: str
    mode: str = "check"
    expected_codes: tuple[int, ...] = (0,)
    reference: str | None = None


def discover(root: Path = ROOT) -> list[Example]:
    expectations: dict[str, tuple[int, ...]] = {}
    for directory in ("typestate", "liquidhaskell"):
        manifest = root / "examples" / directory / "manifest.json"
        if not manifest.exists():
            continue
        for case in json.loads(manifest.read_text())["cases"]:
            if case["expect"] == "reject":
                # Syntax, missing imports and Python crashes must not satisfy
                # an expected refinement/unreachable error.
                codes = {
                    "refinement": (5, 13),
                    "unreachable": (13,),
                    "unused": (12,),
                    "duplicate": (12,),
                    "unrestricted": (12,),
                }
                expectations[f"examples/{directory}/{case['file']}"] = codes[case["error"]]
    expectations["examples/bugs/error.ae"] = (5,)
    expectations["examples/probabilistic/normal_below_7_bad.ae"] = (13,)
    # These open proof specifications intentionally cannot verify before the
    # hole is filled. Check that boundary AND verify a completed control using
    # the benchmark's existing candidate validator, without synthesis search.
    references = {
        "nondecreasing": "0",
        "strict": "x",
        "identity": "x",
        "shift": "x + 1",
        "relu": "if x <= 0 then 0 else x",
    }
    for name in references:
        expectations[f"examples/synthesis/monotonicity/{name}.ae"] = (13,)
    # Paired ML demonstrations deliberately violate linearity, nominal types,
    # or refinement contracts. Keep the expected category specific to each.
    for path in (root / "examples/machine_learning/restrictions").glob("*_invalid.ae"):
        number = int(path.name.split("_", 1)[0])
        code = 12 if number in (0, 1, 2, 3, 4, 5, 9) else 5 if number == 8 else 13
        expectations[path.relative_to(root).as_posix()] = (code,)
    examples = []
    for path in sorted((root / "examples").rglob("*.ae")):
        relative = path.relative_to(root).as_posix()
        mode = "check"
        if relative.startswith("examples/testing/") or (
            relative.startswith("examples/pbt/") and path.name.startswith(("props_", "examples_"))
        ):
            mode = "test"
        reference = references.get(path.stem) if relative.startswith("examples/synthesis/monotonicity/") else None
        examples.append(Example(relative, mode, expectations.get(relative, (0,)), reference))
    missing = expectations.keys() - {example.path for example in examples}
    if missing:
        raise ValueError(f"Missing expected-rejection examples: {sorted(missing)}")
    return examples


def shard_for(path: str, shards: int) -> int:
    return int.from_bytes(hashlib.sha256(path.encode()).digest()[:8], "big") % shards


def command_for(example: Example) -> list[str]:
    mode = ["--test", "--seed", "0"] if example.mode == "test" else ["--check", "--no-main"]
    return [sys.executable, "-m", "aeon", *mode, example.path]


def environment_for(example: Example) -> dict[str, str]:
    env = dict(os.environ)
    env["PYTHONPATH"] = str(ROOT) + os.pathsep + env.get("PYTHONPATH", "")
    # Suites such as LiquidHaskell keep shared modules above their positive/
    # negative subdirectories. Resolve suite-local imports without exposing
    # unrelated suites' identically named helper modules.
    parent = (ROOT / example.path).parent
    containers = []
    while parent != ROOT:
        containers.append(str(parent))
        parent = parent.parent
    if env.get("AEONPATH"):
        containers.append(env["AEONPATH"])
    env["AEONPATH"] = os.pathsep.join(containers)
    return env


def run_one(example: Example, timeout: float, log_dir: Path) -> dict:
    started = time.monotonic()
    log_path = log_dir / f"{example.path}.log"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    env = environment_for(example)
    timed_out = False
    reference_code = None
    with log_path.open("w") as output:
        try:
            result = subprocess.run(
                command_for(example), cwd=ROOT, env=env, stdout=output, stderr=subprocess.STDOUT, timeout=timeout
            )
            code = result.returncode
            if code in example.expected_codes and example.reference is not None:
                remaining = timeout - (time.monotonic() - started)
                if remaining <= 0:
                    raise subprocess.TimeoutExpired(command_for(example), timeout)
                control = subprocess.run(
                    [
                        sys.executable,
                        "-m",
                        "aeon.benchmarks.monotonicity",
                        "--task",
                        Path(example.path).stem,
                        "--task-dir",
                        str((ROOT / example.path).parent),
                        "--candidate",
                        example.reference,
                    ],
                    cwd=ROOT,
                    env=env,
                    stdout=output,
                    stderr=subprocess.STDOUT,
                    timeout=remaining,
                )
                reference_code = control.returncode
        except subprocess.TimeoutExpired:
            code = None
            timed_out = True
    passed = code in example.expected_codes and not timed_out and (example.reference is None or reference_code == 0)
    status = "PASS" if passed else "FAIL"
    print(f"{status} [{example.mode}] {example.path} (exit={code}, {time.monotonic() - started:.1f}s)", flush=True)
    if not passed:
        print(log_path.read_text(errors="replace")[-8000:], flush=True)
    return {
        "path": example.path,
        "mode": example.mode,
        "expected_codes": example.expected_codes,
        "exit_code": code,
        "timeout": timed_out,
        "reference_exit_code": reference_code,
        "passed": passed,
        "seconds": round(time.monotonic() - started, 3),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--shard", type=int, default=0)
    parser.add_argument("--shards", type=int, default=1)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--list", action="store_true")
    parser.add_argument("--failures-from", type=Path, help="Rerun only failures from an earlier results.json")
    parser.add_argument("--report-dir", type=Path, default=Path("example-results"))
    args = parser.parse_args()
    if (
        args.shards < 1
        or not 0 <= args.shard < args.shards
        or args.jobs < 1
        or not math.isfinite(args.timeout)
        or args.timeout <= 0
    ):
        parser.error("Require shards/jobs/timeout > 0 and 0 <= shard < shards")
    examples = discover()
    if args.failures_from:
        failed_paths = {result["path"] for result in json.loads(args.failures_from.read_text()) if not result["passed"]}
        missing = failed_paths - {example.path for example in examples}
        if missing:
            parser.error(f"Previous failures no longer exist: {sorted(missing)}")
        examples = [example for example in examples if example.path in failed_paths]
    examples = [example for example in examples if shard_for(example.path, args.shards) == args.shard]
    if args.list:
        for example in examples:
            print(f"{example.mode}\t{example.path}")
        return 0
    args.report_dir.mkdir(parents=True, exist_ok=True)
    results = []
    with (args.report_dir / "results.jsonl").open("w") as progress, ThreadPoolExecutor(max_workers=args.jobs) as pool:
        pending = [pool.submit(run_one, example, args.timeout, args.report_dir / "logs") for example in examples]
        for future in as_completed(pending):
            result = future.result()
            results.append(result)
            progress.write(json.dumps(result) + "\n")
            progress.flush()
    results.sort(key=lambda result: result["path"])
    (args.report_dir / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    failures = sum(not result["passed"] for result in results)
    print(
        f"{len(results) - failures} passed, {failures} failed, {len(results)} total (shard {args.shard}/{args.shards})"
    )
    return int(failures > 0)


if __name__ == "__main__":
    sys.exit(main())
