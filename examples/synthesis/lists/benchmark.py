"""Run the length-ten specification in isolated processes and check returned lists."""

from __future__ import annotations

import argparse
import contextlib
from datetime import datetime, timezone
import hashlib
import io
import json
import os
from pathlib import Path
import platform
import signal
import subprocess
import sys
import tempfile
import time
from typing import Any

SOURCE = Path(__file__).with_name("size_ten.ae")
ROOT = Path(__file__).resolve().parents[3]
BACKENDS = (
    "tdsyn_enumerative",
    "tdsyn_backward",
    "tdsyn_random",
    "synquid",
    "enumerative",
    "random_search",
    "gp",
    "tactics",
    "rl_mcts",
    "fta",
    "afta",
    "cata",
    "lta",
    "smt",
)


def list_elements(value: object) -> list[int]:
    """Check the actual constructor chain, independently of the SMT size measure."""
    elements: list[int] = []
    while isinstance(value, tuple) and len(value) == 3 and value[0] == "List_cons":
        if type(value[1]) is not int:
            raise ValueError("The synthesized list contains a non-Int element")
        elements.append(value[1])
        value = value[2]
    if value != ("List_nil",):
        raise ValueError("The synthesized value is not a complete List Int")
    return elements


def worker(args: argparse.Namespace) -> None:
    from loguru import logger

    from aeon.core.substitutions import substitution
    from aeon.core.terms import Var
    from aeon.facade.driver import AeonConfig, AeonDriver
    from aeon.synthesis.api import SynthesisNotSuccessful, UnsupportedSynthesisGoal
    from aeon.synthesis.uis.api import SilentSynthesisUI, SynthesisFormat
    from aeon.utils.name import Name

    logger.remove()
    driver = AeonDriver(
        AeonConfig(args.worker, SilentSynthesisUI(), args.budget, synthesis_format=SynthesisFormat.JSON)
    )
    record: dict[str, Any] = {"backend": args.worker, "budget_seconds": args.budget, "seed": args.seed}
    started = time.perf_counter()
    synthesis_started = None
    try:
        errors = list(driver.parse(str(SOURCE)))
        record["compile_seconds"] = time.perf_counter() - started
        if errors:
            raise RuntimeError(str(errors))
        assert driver.has_synth() and len(driver.incomplete_functions) == 1
        target = driver.incomplete_functions[0][0]
        synthesis_started = time.perf_counter()
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            driver.synth()
        record["synthesis_seconds"] = time.perf_counter() - synthesis_started
        record["solution"] = output.getvalue().strip()
        # This source has no main definition. Evaluate ten in the linked program
        # by replacing its synthetic main hole, preserving imported bindings.
        driver.core = substitution(driver.core, Var(target), Name("main", 0))
        value = driver.run()
        record["value"] = repr(value)
        elements = list_elements(value)
        record["elements"] = elements
        record["length"] = len(elements)
        record["status"] = "success" if len(elements) == 10 else "invalid_solution"
    except UnsupportedSynthesisGoal as exc:
        record.update(status="unsupported", error=str(exc))
    except SynthesisNotSuccessful as exc:
        record.update(status="no_solution", error=str(exc))
    except Exception as exc:
        record.update(status="error", error=f"{type(exc).__name__}: {exc}")
    if synthesis_started is not None:
        record.setdefault("synthesis_seconds", time.perf_counter() - synthesis_started)
    args.record.write_text(json.dumps(record, indent=2) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--backend", choices=BACKENDS, action="append", help="Repeat to select backends; default: all")
    parser.add_argument("--budget", type=int, default=10)
    parser.add_argument(
        "--timeout", type=float, default=30, help="Outer wall-clock limit per process, including startup"
    )
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--output", type=Path, help="Save the full JSON report")
    parser.add_argument("--worker", choices=BACKENDS, help=argparse.SUPPRESS)
    parser.add_argument("--record", type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.budget <= 0 or args.timeout <= 0:
        parser.error("budget and timeout must be positive")
    if args.worker:
        worker(args)
        return

    report: dict[str, Any] = {
        "date_utc": datetime.now(timezone.utc).isoformat(),
        "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        "python": platform.python_version(),
        "platform": platform.platform(),
        "budget_seconds": args.budget,
        "outer_timeout_seconds": args.timeout,
        "seed": args.seed,
        "results": [],
    }
    for backend in args.backend or BACKENDS:
        started = time.perf_counter()
        with tempfile.TemporaryDirectory(prefix="aeon-list-ten-") as tmp:
            path = Path(tmp) / "result.json"
            with (Path(tmp) / "worker.log").open("w+") as log:
                command = [
                    sys.executable,
                    str(Path(__file__).resolve()),
                    "--worker",
                    backend,
                    "--budget",
                    str(args.budget),
                    "--seed",
                    str(args.seed),
                    "--record",
                    str(path),
                ]
                process = subprocess.Popen(
                    command,
                    cwd=ROOT,
                    env={**os.environ, "AEON_SEED": str(args.seed), "PYTHONPATH": str(ROOT)},
                    stdout=log,
                    stderr=log,
                    start_new_session=True,
                )
                timed_out = False
                try:
                    process.wait(timeout=args.timeout)
                except subprocess.TimeoutExpired:
                    timed_out = True
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                elapsed = time.perf_counter() - started
                record: dict[str, Any]
                if timed_out or not path.exists():
                    record = {
                        "backend": backend,
                        "status": "outer_timeout" if timed_out else "process_error",
                        "returncode": process.returncode,
                    }
                    log.seek(0)
                    record["log"] = log.read()[-4000:]
                else:
                    record = json.loads(path.read_text())
        record["wall_seconds"] = elapsed
        report["results"].append(record)
        print(f"{backend}: {record['status']} ({elapsed:.2f}s wall)", flush=True)
    if args.output:
        args.output.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
