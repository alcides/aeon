"""Calibrate / time the knapsack GA GPU kernel.

  # Short correctness probe (CPU IR)
  uv run python scripts/bench_knapsack_ga_gpu.py --cpu --generations 200

  # Estimate generations for a 5-minute GPU run, then execute it
  uv run python scripts/bench_knapsack_ga_gpu.py --gpu --target-seconds 300

The GPU path uploads once and launches a single kernel that contains the full
generation loop (no per-generation host sync).
"""

from __future__ import annotations

import argparse
import json
import time

from aeon.bindings.knapsack_ga import make_random_instance, run_cpu, run_gpu, run_random_cpu, run_random_gpu


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cpu", action="store_true")
    parser.add_argument("--gpu", action="store_true")
    parser.add_argument("--n-items", type=int, default=1000)
    parser.add_argument("--pop-size", type=int, default=100)
    parser.add_argument("--generations", type=int, default=0, help="0 = calibrate from --target-seconds")
    parser.add_argument("--target-seconds", type=float, default=300.0)
    parser.add_argument("--calibrate-only", action="store_true", help="Print calibrated generations and exit")
    parser.add_argument("--seed", type=int, default=20260913)
    args = parser.parse_args()
    if not args.cpu and not args.gpu:
        args.gpu = True

    weights, values, capacity = make_random_instance(args.n_items, args.seed)
    generations = args.generations
    backend = "gpu" if args.gpu else "cpu"
    run = run_gpu if args.gpu else run_cpu

    if generations <= 0:
        probe_n = max(1, args.probe_generations)
        t0 = time.perf_counter()
        probe_best = run(weights, values, args.n_items, capacity, args.pop_size, probe_n, args.seed)
        probe_s = time.perf_counter() - t0
        per_gen = probe_s / probe_n
        generations = max(probe_n, int(args.target_seconds / max(per_gen, 1e-12)))
        print(
            json.dumps(
                {
                    "phase": "calibrate",
                    "backend": backend,
                    "probe_generations": probe_n,
                    "probe_seconds": round(probe_s, 4),
                    "seconds_per_generation": per_gen,
                    "target_seconds": args.target_seconds,
                    "calibrated_generations": generations,
                    "probe_best": probe_best,
                },
                indent=2,
            )
        )
        if args.calibrate_only:
            return

    t0 = time.perf_counter()
    best = run(weights, values, args.n_items, capacity, args.pop_size, generations, args.seed)
    elapsed = time.perf_counter() - t0
    print(
        json.dumps(
            {
                "phase": "run",
                "backend": backend,
                "n_items": args.n_items,
                "pop_size": args.pop_size,
                "generations": generations,
                "capacity": capacity,
                "best": best,
                "seconds": round(elapsed, 3),
                "single_kernel": True,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
