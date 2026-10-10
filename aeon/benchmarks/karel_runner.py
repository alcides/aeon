"""Run imported Karel tasks as Aeon programs, with isolated per-task deadlines."""

import argparse
from collections import deque
from concurrent.futures import Future, ThreadPoolExecutor
from dataclasses import replace
import itertools
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time

from aeon.benchmarks.karel import decode_world, task_source
from aeon.bindings.karel import fitness


def candidate_function(driver):
    """Get the compiled Aeon closure without invoking main or exporting Python."""
    from aeon.backend.evaluator import eval as evaluate
    from aeon.backend.python_export import find_binding
    from aeon.core.terms import Let, Rec, Var

    binding = find_binding(driver.core, "solve")
    if binding is None:
        raise ValueError("missing solve binding")

    def return_candidate(term):
        if isinstance(term, (Let, Rec)):
            return replace(term, body=return_candidate(term.body))
        return Var(binding[0])

    return evaluate(return_candidate(driver.core), driver.evaluation_ctx)


def run_task(payload: dict) -> dict:
    from aeon.facade.driver import AeonConfig, AeonDriver
    from aeon.synthesis.uis.api import SilentSynthesisUI

    observed = payload["observed"]
    heldout = payload["heldout"]
    with tempfile.TemporaryDirectory(prefix="aeon-published-karel-") as directory:
        data = Path(directory) / "observed.json"
        data.write_text(json.dumps(observed), encoding="utf-8")
        expression = payload["expression"] if payload["mode"] == "validate" else None
        code = task_source(data, expression)
        program_path = Path(directory) / "task.ae"
        program_path.write_text(code, encoding="utf-8")
        driver = AeonDriver(
            AeonConfig(
                synthesizer=payload["synthesizer"],
                synthesis_ui=SilentSynthesisUI(),
                synthesis_budget=payload["budget"],
                no_main=True,
            )
        )
        errors = list(driver.parse(str(program_path)))
        if errors:
            raise ValueError("; ".join(str(error) for error in errors))
        if expression is None:
            if not driver.has_synth():
                raise ValueError("missing synthesis hole")
            driver.synth()
        program = candidate_function(driver)
        observed_pairs = tuple((decode_world(a), decode_world(b)) for a, b in observed["pairs"])
        heldout_pairs = tuple((decode_world(a), decode_world(b)) for a, b in heldout["pairs"])
        observed_failures = fitness(program, observed_pairs)
        heldout_failures = fitness(program, heldout_pairs)
        return {
            "status": "ok",
            "observed_failures": observed_failures,
            "heldout_failures": heldout_failures,
            "consistent": observed_failures == 0,
            "generalizes": observed_failures == 0 and heldout_failures == 0,
        }


def run_isolated(payload: dict, deadline: float) -> dict:
    """Kill a stuck compiler/search/candidate, not just an explicitly fueled loop."""
    started = time.monotonic()
    try:
        process = subprocess.run(
            [sys.executable, "-m", "aeon.benchmarks.karel_runner", "--worker"],
            input=json.dumps(payload),
            text=True,
            capture_output=True,
            timeout=deadline,
        )
        if process.returncode:
            result = {"status": "error", "error": process.stderr[-2000:]}
        else:
            # Synthesizers may print diagnostics even with a silent UI.
            result = json.loads(process.stdout.strip().splitlines()[-1])
    except subprocess.TimeoutExpired:
        result = {"status": "timeout"}
    except (ValueError, IndexError) as error:
        result = {"status": "error", "error": str(error)}
    return {**result, "elapsed_seconds": time.monotonic() - started}


def isolated_results(payloads, jobs: int, deadline: float):
    """Bound the queue to jobs tasks, even for a million-record streaming split."""
    iterator = iter(payloads)
    pending: deque[tuple[dict, Future[dict]]] = deque()
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        for payload in itertools.islice(iterator, jobs):
            pending.append((payload, executor.submit(run_isolated, payload, deadline)))
        while pending:
            payload, future = pending.popleft()
            yield {"id": payload["observed"]["id"], "guid": payload["observed"]["guid"], **future.result()}
            following = next(iterator, None)
            if following is not None:
                pending.append((following, executor.submit(run_isolated, following, deadline)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worker", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--split", type=Path)
    parser.add_argument("--results", type=Path)
    parser.add_argument("--mode", choices=["validate", "synthesize"], default="validate")
    parser.add_argument("--synthesizer", default="enumerative")
    parser.add_argument("--budget", type=int, default=60)
    parser.add_argument("--deadline", type=float, default=120)
    parser.add_argument("--jobs", type=int, default=1, help="Concurrent isolated tasks; bounded memory")
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--count", type=int, help="Default: all tasks, not a smoke subset")
    args = parser.parse_args()
    if args.worker:
        from loguru import logger

        logger.disable("aeon")
        try:
            print(json.dumps(run_task(json.load(sys.stdin))))
        except Exception as error:
            print(json.dumps({"status": "error", "error": f"{type(error).__name__}: {error}"}))
        return
    if args.split is None or args.results is None:
        parser.error("--split and --results are required")
    if (
        args.start < 0
        or (args.count is not None and args.count <= 0)
        or args.budget < 0
        or args.deadline <= 0
        or args.jobs < 1
    ):
        parser.error("invalid range or budget")
    manifest = json.loads((args.split / "manifest.json").read_text(encoding="utf-8"))
    stop = manifest["tasks"] if args.count is None else args.start + args.count
    if not args.start < stop <= manifest["tasks"]:
        parser.error("task range outside manifest")
    summary = {
        "mode": args.mode,
        "tasks": 0,
        "consistent": 0,
        "generalizes": 0,
        "errors": 0,
        "start": args.start,
        "source_jsonl_sha256": manifest["source_jsonl_sha256"],
    }
    with (
        (args.split / "observed.jsonl").open(encoding="utf-8") as observed,
        (args.split / "heldout.jsonl").open(encoding="utf-8") as heldout,
        (args.split / "references.jsonl").open(encoding="utf-8") as references,
        args.results.open("x", encoding="utf-8") as output,
    ):
        records = itertools.zip_longest(observed, heldout, references)
        selected = itertools.islice(records, args.start, stop)

        def payloads():
            for index, lines in enumerate(selected, args.start):
                if any(line is None for line in lines):
                    raise ValueError("inconsistent split lengths")
                specification, evaluation, reference = (json.loads(line) for line in lines)
                if not specification["id"] == evaluation["id"] == reference["id"] == index:
                    raise ValueError("misaligned task identities")
                if not specification["guid"] == evaluation["guid"] == reference["guid"]:
                    raise ValueError("misaligned task GUIDs")
                payload = {
                    "mode": args.mode,
                    "synthesizer": args.synthesizer,
                    "budget": args.budget,
                    "observed": specification,
                    "heldout": evaluation,
                }
                if args.mode == "validate":
                    payload["expression"] = reference["expression"]
                yield payload

        for result in isolated_results(payloads(), args.jobs, args.deadline):
            output.write(json.dumps(result) + "\n")
            output.flush()
            summary["tasks"] += 1
            summary["consistent"] += int(result.get("consistent", False))
            summary["generalizes"] += int(result.get("generalizes", False))
            summary["errors"] += int(result["status"] != "ok")
            print(json.dumps(result), flush=True)
        if summary["tasks"] != stop - args.start:
            raise ValueError("truncated split")
        if stop == manifest["tasks"] and next(records, None) is not None:
            raise ValueError("split contains more tasks than manifest")
    summary["full_split"] = args.start == 0 and summary["tasks"] == manifest["tasks"]
    summary["all_references_validated"] = (
        args.mode == "validate" and summary["full_split"] and summary["generalizes"] == summary["tasks"]
    )
    args.results.with_suffix(args.results.suffix + ".summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary), flush=True)
    if args.mode == "validate" and summary["generalizes"] != summary["tasks"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
