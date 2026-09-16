"""Time the functional knapsack GA example.

uv run python scripts/bench_knapsack_ga_gpu.py
"""

from __future__ import annotations

import json
import time
from pathlib import Path

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    path = ROOT / "examples/knapsack_ga.ae"
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
                "result": result,
                "seconds": round(elapsed, 3),
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
