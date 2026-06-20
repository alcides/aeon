"""Benchmark IntHoleCP (OR-Tools CP-SAT) against the GP backend.

Each benchmark in ``examples/synthesis/ortools/`` jointly optimises a program's
Int holes against an integer objective; every one has known optimum value 0
(or a known constrained optimum). CP-SAT solves them *exactly*; the grammar
backend (gp) has no per-hole signal on these holes — the objective lives on a
hole-free function — so it cannot optimise them. We report the achieved
objective (lower = better).

Run: uv run python scripts/bench_ortools.py
"""

from __future__ import annotations

import sys
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from aeon.core.substitutions import substitution
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.entrypoint import _make_fitness, synthesize_holes
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.synthesis.uis.api import SilentSynthesisUI, SynthesisFormat

setup_logger()

BUDGET = 5.0
BENCH_DIR = Path(__file__).resolve().parent.parent / "examples" / "synthesis" / "ortools"
BENCHMARKS = [
    "int_sphere",
    "int_booth",
    "int_constrained",
    "int_let",
    "float_quadratic",
    "array_int",
    "array_float",
]
BACKENDS = ["ortools", "gp"]


def achieved_objective(driver: AeonDriver, mapping: dict) -> float | None:
    goals = [g for d in driver.metadata.values() for g in d.get("goals", [])]
    if not goals or not mapping or any(v is None for v in mapping.values()):
        return None
    prog = driver.core
    for name, term in mapping.items():
        prog = substitution(prog, term, name)
    try:
        return float(sum(_make_fitness(g, driver.evaluation_ctx)(prog) for g in goals))
    except Exception:  # noqa: BLE001
        return None


def run(name: str, backend: str) -> dict[str, Any]:
    src = (BENCH_DIR / f"{name}.ae").read_text()
    cfg = AeonConfig(
        synthesizer=backend,
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=int(BUDGET),
        synthesis_format=SynthesisFormat.DEFAULT,
    )
    driver = AeonDriver(cfg)
    try:
        errs = list(driver.parse(aeon_code=src))
    except Exception as e:  # noqa: BLE001
        return {"obj": None, "time": 0.0, "error": f"parse: {type(e).__name__}: {e}"}
    if errs:
        return {"obj": None, "time": 0.0, "error": f"parse: {errs[0]}"}
    targets = incomplete_functions_and_holes(driver.typing_ctx, driver.core)
    t0 = time.monotonic()
    try:
        mapping = synthesize_holes(
            driver.typing_ctx,
            driver.evaluation_ctx,
            driver.core,
            targets,
            driver.metadata,
            make_synthesizer(backend),
            BUDGET,
            SilentSynthesisUI(),
        )
    except Exception as e:  # noqa: BLE001
        return {"obj": None, "time": time.monotonic() - t0, "error": f"{type(e).__name__}: {e}"}
    return {"obj": achieved_objective(driver, mapping), "time": time.monotonic() - t0, "error": None}


def main() -> None:
    print(f"budget={BUDGET}s\n")
    print(f"{'benchmark':<16} {'backend':<9} {'objective':>14}  {'time':>6}")
    print("-" * 50)
    wins = {b: 0 for b in BACKENDS}
    for name in BENCHMARKS:
        results: dict[str, float | None] = {}
        for backend in BACKENDS:
            r = run(name, backend)
            results[backend] = r["obj"]
            shown = "—" if r["obj"] is None else f"{r['obj']:.3g}"
            note = f"  ({r['error'][:24]})" if r["error"] else ""
            print(f"{name:<16} {backend:<9} {shown:>14}  {r['time']:>5.1f}s{note}")
        valid = {b: o for b, o in results.items() if o is not None}
        if valid:
            wins[min(valid, key=valid.get)] += 1
        print()
    print("=" * 50)
    print("Wins (lowest objective): " + "  ".join(f"{b}={wins[b]}" for b in BACKENDS))


if __name__ == "__main__":
    main()
