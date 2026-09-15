"""Time the knapsack GA examples.

uv run python scripts/bench_knapsack_ga_gpu.py --cpu
uv run python scripts/bench_knapsack_ga_gpu.py --gpu
"""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cpu", action="store_true")
    parser.add_argument("--gpu", action="store_true")
    args = parser.parse_args()
    if not args.cpu and not args.gpu:
        args.cpu = True

    path = ROOT / ("examples/llvm/gpu/knapsack_ga.ae" if args.gpu else "examples/llvm/knapsack_ga_cpu.ae")
    cfg = AeonConfig(synthesizer="none", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(cfg)
    errors = driver.parse(filename=str(path))
    if errors:
        raise RuntimeError(errors)
    t0 = time.perf_counter()
    result = driver.run()
    elapsed = time.perf_counter() - t0
    print(
        json.dumps(
            {
                "example": str(path.relative_to(ROOT)),
                "backend": "gpu" if args.gpu else "cpu",
                "result": result,
                "seconds": round(elapsed, 3),
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
