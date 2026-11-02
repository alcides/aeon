"""Reproduce bounded DP transformations, emitted-source checks and ablations."""

import argparse
import hashlib
import json
import re
from pathlib import Path
import subprocess

from loguru import logger

from aeon.backend.evaluator import eval as evaluate
from aeon.core.terms import Var
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.sugar.lifting import lift
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.fitness_eval import set_program_tail
from aeon.synthesis.identification import incomplete_functions_and_holes, iterate_top_level
from aeon.synthesis.modules.dp_gp import DPSynthesizer
from aeon.synthesis.modules.dp_gp.emission import apply, integer
from aeon.synthesis.modules.dp_gp.model import Config
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.pprint import pretty_print_sterm


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--budget", type=float, default=30)
    parser.add_argument("--seeds", type=int, nargs="+", default=[0, 1, 2])
    parser.add_argument("--proposals", type=int, default=160)
    args = parser.parse_args()
    logger.remove()
    root = Path(__file__).resolve().parents[1]
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    dirty = bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=root, text=True).strip())
    args.output.mkdir(parents=True, exist_ok=True)
    results = []
    for case in ("knapsack", "path"):
        source = (root / f"examples/synthesis/dp_gp/{case}.ae").read_text()
        for seed in args.seeds:
            record = {
                "case": case,
                "seed": seed,
                "budget": args.budget,
                "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
            }
            try:
                driver = AeonDriver(AeonConfig("dp_gp", SilentSynthesisUI(), args.budget, no_main=True))
                errors = driver.parse(aeon_code=source)
                if errors:
                    raise ValueError(str(errors))
                backend = DPSynthesizer(config=Config(seed=seed, proposals=args.proposals))
                mapping = synthesize_holes(
                    driver.typing_ctx,
                    driver.evaluation_ctx,
                    driver.core,
                    incomplete_functions_and_holes(driver.typing_ctx, driver.core),
                    driver.metadata,
                    backend,
                    args.budget,
                    SilentSynthesisUI(),
                )
                candidate = next(iter(mapping.values()))
                if candidate is None:
                    raise ValueError("No fully checked candidate")
                body = pretty_print_sterm(lift(candidate), top_level=False)
                body = re.sub(r"\bTrue\b", "true", body)
                body = re.sub(r"\bFalse\b", "false", body)
                for internal, public in (
                    ("DP_solve", "DP.solve"),
                    ("DP_get", "DP.get"),
                    ("DPVector_cell", "DPVector.cell"),
                    ("DPVector_vnil", "DPVector.vnil"),
                ):
                    body = body.replace(internal, public)
                emitted = "\n".join(line for line in source.splitlines() if not line.startswith("@dp_gp"))
                emitted = emitted.replace("?algorithm", body) + "\n"
                output = args.output / f"{case}-seed-{seed}.ae"
                output.write_text(emitted)
                # A new compiler invocation must accept and execute the saved
                # source, not merely the original in-memory term.
                fresh = AeonDriver(AeonConfig("gp", SilentSynthesisUI(), 0, no_main=True))
                errors = fresh.parse(aeon_code=emitted)
                if errors:
                    raise ValueError("Emitted source does not recompile: " + str(errors))
                functions = {d.var_name.name: d.var_name for d in iterate_top_level(fresh.core)}
                checked = 0
                for values in backend.last_report["instances"]:
                    actual = []
                    for name in ("reference", "optimized"):
                        call = apply(Var(functions[name]), *(integer(v) for v in values))
                        actual.append(evaluate(set_program_tail(fresh.core, call), fresh.evaluation_ctx))
                    if actual[0] != actual[1]:
                        raise ValueError(f"Emitted source mismatch on {values}: {actual}")
                    checked += 1
                record.update(
                    status="completed",
                    report=backend.last_report,
                    emitted_file=output.name,
                    recompiled_instances=checked,
                )
            except Exception as exc:
                record.update(status="failed", error=f"{type(exc).__name__}: {exc}")
            results.append(record)
            print(case, seed, record["status"], record.get("error", ""), flush=True)
    report = {
        "revision": revision,
        "dirty": dirty,
        "proposals_per_epoch": args.proposals,
        "protocol": "fixed GP population 32; seed; disjoint training/checking/held-out instances; exhaustive final check",
        "results": results,
    }
    (args.output / "results.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
