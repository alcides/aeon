"""Benchmark GenomicNG (Nevergrad/NGOpt) against the GP backend.

For each example we run both synthesizers with the same time budget and seed,
recording every candidate the synthesizer evaluates through a SynthesisUI. We
report:
  - success: a valid completion was found
  - best:    best (minimisation-oriented) objective sum among valid candidates
             (0.0 for validate-only goals; lower is better)
  - valid/total: how many evaluated candidates were valid

Run: uv run python scripts/bench_genomic_ng.py
"""

from __future__ import annotations

import sys
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from aeon.logger.logger import setup_logger
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.grammar.ge_synthesis import GESynthesizer
from aeon.synthesis.grammar.genomic_ng import GenomicNGSynthesizer
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.uis.api import SynthesisUI
from tests.driver import check_and_return_core

setup_logger()

BUDGET = 5.0
SEEDS = [1, 2]
EXAMPLES = [
    "dummy",
    "int",
    "linear_equation",
    "quadratic",
    "system_equations",
    "bank_deposit",
    "coin",
    "pizza",
    "stock_profit",
    "multiobjective",
]
ROOT = Path(__file__).resolve().parent.parent
EX_DIR = ROOT / "examples" / "synthesis"


class RecordingUI(SynthesisUI):
    """Tracks best valid fitness and valid/total counts across a run."""

    def __init__(self) -> None:
        self.total = 0
        self.valid = 0
        self.best: float | None = None

    def start(self, *a: Any, **k: Any) -> None:
        pass

    def register(self, solution: Any, quality: Any, elapsed_time: float, is_best: bool) -> None:
        self.total += 1
        comps = getattr(quality, "fitness_components", None)
        is_valid = getattr(quality, "valid", True)
        if not is_valid or comps is None:
            return
        self.valid += 1
        score = float(sum(comps))
        if self.best is None or score < self.best:
            self.best = score

    def end(self, *a: Any, **k: Any) -> None:
        pass


def run_one(source: str, make_synth: Any, seed: int) -> dict[str, Any]:
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    incomplete = incomplete_functions_and_holes(ctx, core_ast_anf)
    ui = RecordingUI()
    t0 = time.monotonic()
    mapping = synthesize_holes(
        ctx, ectx, core_ast_anf, incomplete, metadata, synthesizer=make_synth(seed), budget=BUDGET, ui=ui
    )
    elapsed = time.monotonic() - t0
    success = bool(mapping) and all(v is not None for v in mapping.values())
    return {"success": success, "best": ui.best, "valid": ui.valid, "total": ui.total, "time": elapsed}


def main() -> None:
    backends = {
        "gp": lambda seed: GESynthesizer(method="genetic_programming", seed=seed),
        "ng(NGOpt)": lambda seed: GenomicNGSynthesizer(optimizer="NGOpt", seed=seed),
    }

    print(f"budget={BUDGET}s  seeds={SEEDS}\n")
    header = f"{'example':<18} {'backend':<10} result"
    print(header)
    print("-" * len(header) + "-" * 20)

    wins = {"gp": 0, "ng(NGOpt)": 0, "tie": 0}
    for name in EXAMPLES:
        src = (EX_DIR / f"{name}.ae").read_text()
        agg: dict[str, dict[str, Any]] = {}
        for bname, make in backends.items():
            succ = 0
            bests: list[float] = []
            totals = 0
            valids = 0
            tsum = 0.0
            for seed in SEEDS:
                try:
                    r = run_one(src, make, seed)
                except Exception as e:  # noqa: BLE001 - benchmark should not abort on one cell
                    print(f"{name:<18} {bname:<10} ERROR {type(e).__name__}: {e}")
                    r = {"success": False, "best": None, "valid": 0, "total": 0, "time": 0.0}
                succ += int(r["success"])
                if r["best"] is not None:
                    bests.append(r["best"])
                totals += r["total"]
                valids += r["valid"]
                tsum += r["time"]
            agg[bname] = {
                "solved": succ,
                "best": min(bests) if bests else None,
                "valid": valids,
                "total": totals,
                "time": tsum / len(SEEDS),
            }
            ok = f"{succ}/{len(SEEDS)}"
            best = "—" if agg[bname]["best"] is None else f"{agg[bname]['best']:.3g}"
            print(
                f"{name:<18} {bname:<10} solved={ok}  best={best:>8}  "
                f"avg_time={agg[bname]['time']:.1f}s  (internal valid={valids}/{totals})"
            )

        # Winner: higher solve-rate; tie-break on average time, then objective.
        g, n = agg["gp"], agg["ng(NGOpt)"]
        if g["solved"] != n["solved"]:
            winner = "gp" if g["solved"] > n["solved"] else "ng(NGOpt)"
        elif g["solved"] == 0:
            winner = "tie"  # neither solved
        elif abs(g["time"] - n["time"]) > 0.2:
            winner = "gp" if g["time"] < n["time"] else "ng(NGOpt)"
        else:
            winner = "tie"
        wins[winner] += 1
        print(f"{'':<18} {'-> winner':<10} {winner}\n")

    print("=" * 40)
    print(f"Wins: gp={wins['gp']}  ng(NGOpt)={wins['ng(NGOpt)']}  tie={wins['tie']}")


if __name__ == "__main__":
    main()
