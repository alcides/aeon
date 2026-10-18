"""Run relational proof tasks through Aeon's existing candidate proof harness."""

import argparse
from dataclasses import asdict
import json
from pathlib import Path
import time

TASKS = {"nondecreasing", "strict", "identity", "shift", "relu"}


def is_monotonicity_case(source, path):
    path = Path(path).resolve()
    directory = Path(source).resolve() / "examples/synthesis/monotonicity"
    return path.parent == directory and path.suffix == ".ae" and path.stem in TASKS


def run(path, backend, budget, emit, benchmark_factory=None):
    if benchmark_factory is None:
        from aeon.benchmarks.monotonicity import MonotonicityBenchmark

        benchmark_factory = MonotonicityBenchmark
    path = Path(path)
    emit("start", target="f", budget=str(budget), entrypoint="monotonicity", proof_required=True)
    benchmark = benchmark_factory(path.stem, path.parent)
    result = benchmark.synthesize(backend=backend, budget=budget)
    # Retain an independent final gate before reporting any filled hole.
    proof = benchmark.verify(result.candidate) if result is not None else None
    accepted = proof is not None and proof.accepted
    holes = {"?body": proof.candidate} if accepted else {}
    emit("proof", task=path.stem, **(asdict(proof) if proof else {"status": "no_solution"}))
    emit(
        "end",
        target="f",
        solution=proof.candidate if accepted else None,
        quality={"components": [], "valid": accepted},
        objective_verified=accepted,
    )
    emit("results", holes=holes)
    print("Synthesized holes:")
    print(json.dumps(holes))
    return 0 if accepted else 2


def main(argv, events):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-main", action="store_true")
    parser.add_argument("--budget", type=float, default=5)
    parser.add_argument("-s", "--synthesizer", default="random_search")
    parser.add_argument("--synthesis-format", choices=["json"], default="json")
    parser.add_argument("filename", type=Path)
    args = parser.parse_args(argv)
    from aeon.logger.logger import setup_logger
    from loguru import logger

    setup_logger()
    logger.remove()
    start = time.monotonic()

    def emit(event, **data):
        with Path(events).open("a") as stream:
            stream.write(json.dumps({"event": event, "wall_s": time.monotonic() - start, **data}) + "\n")

    return run(args.filename, args.synthesizer, args.budget, emit)


# Use the repository-owned adapter for fixed snapshots, preserving old replay.
try:
    from aeon.benchmarks.monotonicity_runner import main as repository_main, run as repository_run
except ModuleNotFoundError as exc:
    if exc.name != "aeon.benchmarks.monotonicity_runner":
        raise
else:
    main = repository_main
    run = repository_run
