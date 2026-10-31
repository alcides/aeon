"""Inventory, import, run and independently verify BNSynth benchmarks."""

import argparse
import json
from pathlib import Path
import os
import math

from aeon.benchmarks.bounded_boolean.corpus import (
    ROOT,
    PAPER_SCHEDULE,
    digest,
    emit,
    fetch,
    load_case,
    regenerate,
    verify_manifest,
)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    for name in ("inventory", "import", "fetch"):
        sub.add_parser(name)
    for name in ("run", "audit"):
        command = sub.add_parser(name)
        command.add_argument("--case", action="append", dest="cases")
        command.add_argument("--backend", action="append", dest="backends")
        command.add_argument("--bound", type=int, default=5)
        command.add_argument("--budget", type=float, default=5)
        command.add_argument("--wall-timeout", type=float)
        command.add_argument("--memory-mb", type=int, default=4096)
        command.add_argument("--seed", type=int, action="append", dest="seeds")
        command.add_argument("--output", type=Path, required=True)
        command.add_argument("--no-resume", action="store_true")
        command.add_argument("--paper-schedule", action="store_true")
    verify = sub.add_parser("verify")
    verify.add_argument("result", type=Path)
    worker = sub.add_parser("_worker")
    worker.add_argument("request", type=Path)
    worker.add_argument("destination", type=Path)
    args = parser.parse_args(argv)
    if args.command == "_worker":
        request = json.loads(args.request.read_text())
        if os.name == "posix":
            import resource

            memory = request["memory_mb"] * 1024 * 1024
            resource.setrlimit(resource.RLIMIT_AS, (memory, memory))
            cpu = math.ceil(request["wall_timeout"]) + 1
            resource.setrlimit(resource.RLIMIT_CPU, (cpu, cpu))
        from aeon.benchmarks.bounded_boolean.runner import worker as run_worker

        run_worker(request, args.destination)
        return 0
    if args.command == "fetch":
        fetch()
        return 0
    if args.command == "import":
        print(json.dumps(regenerate()["inventory"], indent=2))
        return 0
    manifest = verify_manifest()
    if args.command == "inventory":
        print(json.dumps(manifest["inventory"], indent=2))
        return 0
    cases = {c["id"]: c for c in manifest["cases"]}
    if args.command == "verify":
        from aeon.benchmarks.bounded_boolean.checker import CheckFailure, check
        from aeon.benchmarks.bounded_boolean.runner import candidate_digest

        saved = json.loads(args.result.read_text())
        config = saved["config"]
        case = cases[config["task"]]
        circuit = load_case(case)
        expected = digest(emit(circuit, case["id"], config["bound"]).encode())
        if (
            config["source_sha256"] != expected
            or config["verilog_sha256"] != digest((ROOT / "upstream" / case["source"]).read_bytes())
            or config["y_sha256"] != digest((ROOT / "upstream" / case["y_file"]).read_bytes())
        ):
            parser.error("saved result belongs to different source bytes or configuration")
        if "outputs" not in saved:
            parser.error("result contains no candidate; bounded UNSAT is not a solution certificate")
        if saved.get("candidate_sha256") != candidate_digest(saved["outputs"]):
            parser.error("candidate hash mismatch")
        try:
            result = check(circuit, saved["outputs"], config["bound"])
        except CheckFailure as exc:
            result = {"status": exc.status, "reason": str(exc)}
        print(json.dumps(result, indent=2))
        return 0 if result["status"] == "verified_solved" else 1
    from aeon.benchmarks.bounded_boolean.runner import identity, run_one, summary, write_json

    selected = args.cases or list(cases)
    if any(case not in cases for case in selected):
        parser.error("unknown case; use inventory/manifest.json for task IDs")
    if (
        args.bound < 0
        or args.budget <= 0
        or args.memory_mb <= 0
        or (args.wall_timeout is not None and args.wall_timeout <= 0)
    ):
        parser.error("bound must be nonnegative and budgets positive")
    provenance = identity()
    results = []
    for case_id in selected:
        case = cases[case_id]
        for backend in args.backends or ["boolean_bounded"]:
            for seed in args.seeds or [0]:
                for bound, budget in PAPER_SCHEDULE if args.paper_schedule else [(args.bound, args.budget)]:
                    result = run_one(
                        case,
                        backend,
                        args.output,
                        bound=bound,
                        budget=budget,
                        wall_timeout=args.wall_timeout or budget + 30,
                        seed=seed,
                        audit=args.command == "audit",
                        resume=not args.no_resume,
                        provenance=provenance,
                        memory_mb=args.memory_mb,
                    )
                    results.append(result)
                    print(f"{case_id} {backend} K={bound} seed={seed}: {result['status']}", flush=True)
                    write_json(
                        args.output / "summary.json",
                        {
                            "corpus_revision": manifest["revision"],
                            "manifest_sha256": digest((ROOT / "manifest.json").read_bytes()),
                            **summary(results),
                            "results": results,
                        },
                    )
                    if result["status"] == "verified_solved":
                        break
    print(json.dumps(summary(results), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
