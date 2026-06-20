"""Benchmark FloatHoleNG on classic Nevergrad test functions.

Each benchmark in ``examples/synthesis/float_ng/`` is a program whose holes are
all ``Float`` constants jointly minimising a well-known optimisation surface
(sphere, Rosenbrock, Booth, Matyas, Rastrigin, Ackley). Every function has
global minimum value 0, so the *achieved objective value* is directly the
quality (lower = better; 0 = optimum found).

We compare:
  - ng_float       FloatHoleNG with NGOpt
  - ng_float_cma   FloatHoleNG with CMA-ES
  - gp             the grammar-based GP backend

gp is included to show the gap: the objective lives on a function without a
hole, so the per-hole grammar search has no signal on these holes and cannot
optimise them — exactly the niche FloatHoleNG fills.

Run: uv run python scripts/bench_float_ng.py
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

BUDGET = 3.0
SEEDS = [1, 2]
SOLVED_THRESHOLD = 1e-3
BENCH_DIR = Path(__file__).resolve().parent.parent / "examples" / "synthesis" / "float_ng"
BENCHMARKS = ["sphere", "rosenbrock", "booth", "matyas", "rastrigin", "ackley", "sphere_array"]
BACKENDS = ["ng_float", "ng_float_cma", "gp"]


def achieved_objective(driver: AeonDriver, mapping: dict) -> float | None:
    """Objective value of the program with its holes filled by ``mapping``."""
    goals = [g for d in driver.metadata.values() for g in d.get("goals", [])]
    if not goals or any(v is None for v in mapping.values()):
        return None
    prog = driver.core
    for name, term in mapping.items():
        prog = substitution(prog, term, name)
    try:
        return float(sum(_make_fitness(g, driver.evaluation_ctx)(prog) for g in goals))
    except Exception:
        return None


def run(name: str, backend: str, seed: int) -> dict[str, Any]:
    src = (BENCH_DIR / f"{name}.ae").read_text()
    cfg = AeonConfig(
        synthesizer=backend,
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=int(BUDGET),
        synthesis_format=SynthesisFormat.DEFAULT,
    )
    driver = AeonDriver(cfg)
    try:
        # parse() returns elaboration/type errors as a list, but a lexer/parser
        # error is raised — guard both so one bad file can't abort the suite.
        errs = list(driver.parse(aeon_code=src))
    except Exception as e:  # noqa: BLE001
        return {"obj": None, "time": 0.0, "error": f"parse: {type(e).__name__}: {e}"}
    if errs:
        return {"obj": None, "time": 0.0, "error": f"parse: {errs[0]}"}
    targets = incomplete_functions_and_holes(driver.typing_ctx, driver.core)
    synth = make_synthesizer(backend)
    # FloatHoleNG seed is on the instance; set it for reproducibility.
    if hasattr(synth, "seed"):
        synth.seed = seed
    t0 = time.monotonic()
    try:
        mapping = synthesize_holes(
            driver.typing_ctx,
            driver.evaluation_ctx,
            driver.core,
            targets,
            driver.metadata,
            synth,
            BUDGET,
            SilentSynthesisUI(),
        )
    except Exception as e:  # noqa: BLE001
        return {"obj": None, "time": time.monotonic() - t0, "error": f"{type(e).__name__}: {e}"}
    return {"obj": achieved_objective(driver, mapping), "time": time.monotonic() - t0, "error": None}


def main() -> None:
    print(f"budget={BUDGET}s  seeds={SEEDS}  solved if objective < {SOLVED_THRESHOLD}\n")
    print(f"{'benchmark':<12} {'backend':<13} {'best objective':>16}  {'solved':>7}")
    print("-" * 54)
    wins = {b: 0 for b in BACKENDS}
    for name in BENCHMARKS:
        best_per_backend: dict[str, float | None] = {}
        for backend in BACKENDS:
            objs = []
            for seed in SEEDS:
                r = run(name, backend, seed)
                if r["error"]:
                    print(f"{name:<12} {backend:<13} {'ERROR':>16}  {r['error'][:30]}")
                elif r["obj"] is not None:
                    objs.append(r["obj"])
            best = min(objs) if objs else None
            best_per_backend[backend] = best
            shown = "—" if best is None else f"{best:.3e}"
            solved = "yes" if best is not None and best < SOLVED_THRESHOLD else "no"
            print(f"{name:<12} {backend:<13} {shown:>16}  {solved:>7}")
        # Winner = lowest achieved objective.
        valid = {b: o for b, o in best_per_backend.items() if o is not None}
        if valid:
            wins[min(valid, key=valid.get)] += 1
        print()
    print("=" * 54)
    print("Wins (lowest objective): " + "  ".join(f"{b}={wins[b]}" for b in BACKENDS))


if __name__ == "__main__":
    main()
