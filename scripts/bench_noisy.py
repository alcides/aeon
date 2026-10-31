"""Small matched-budget comparison; no claim to reproduce POPL 2016 results."""

import argparse
from dataclasses import replace
import hashlib
import json
from pathlib import Path
import subprocess

from loguru import logger

from aeon.backend.evaluator import eval as aeon_eval
from aeon.core.substitutions import substitution
from aeon.core.terms import Application, Literal, Var
from aeon.core.types import t_int
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.fitness_eval import set_program_tail
from aeon.synthesis.identification import incomplete_functions_and_holes, iterate_top_level
from aeon.synthesis.modules.noisy import NoisySynthesizer
from aeon.synthesis.modules.noisy.model import Config
from aeon.synthesis.uis.api import SilentSynthesisUI


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--budget", type=float, default=3)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    logger.remove()
    root = Path(__file__).resolve().parents[1]
    config = Config(rounds=4, candidates_per_round=8)
    results = []
    # Held-out inputs/outputs are used only after synthesis, never in metadata
    # or the component library. No tuning is performed on the held-out task.
    for case, split, function, expected in (
        ("identity", "development", "identity", (4, 10, 50)),
        ("precise", "development", "identity", (4, 10, 50)),
        ("successor", "held_out_task", "successor", (5, 11, 51)),
    ):
        source = (root / "examples/synthesis/noisy" / f"{case}.ae").read_text()
        for mode in ("full", "uniform", "adaptive"):
            driver = AeonDriver(AeonConfig("noisy", SilentSynthesisUI(), args.budget, no_main=True))
            engine = NoisySynthesizer(args.seed, replace(config, sampler=mode))
            record = {
                "case": case,
                "split": split,
                "sampler": mode,
                "seed": args.seed,
                "budget": args.budget,
                "candidate_limit": config.rounds * config.candidates_per_round,
                "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
            }
            try:
                errors = driver.parse(aeon_code=source)
                if errors:
                    raise ValueError(str(errors))
                targets = incomplete_functions_and_holes(driver.typing_ctx, driver.core)
                mapping = synthesize_holes(
                    driver.typing_ctx,
                    driver.evaluation_ctx,
                    driver.core,
                    targets,
                    driver.metadata,
                    engine,
                    args.budget,
                    SilentSynthesisUI(),
                )
                completed = driver.core
                for name, term in mapping.items():
                    if term is None:
                        raise ValueError("No completed candidate")
                    completed = substitution(completed, term, name)
                name = next(r.var_name for r in iterate_top_level(completed) if r.var_name.name == function)
                actual = [
                    aeon_eval(
                        set_program_tail(completed, Application(Var(name), Literal(value, t_int))),
                        driver.evaluation_ctx,
                    )
                    for value in (4, 10, 50)
                ]
                record.update(
                    status="completed",
                    report=engine.last_report.as_dict(),
                    candidate={str(n): str(t) for n, t in mapping.items()},
                    held_out_inputs=[4, 10, 50],
                    held_out_expected=expected,
                    held_out_actual=actual,
                    held_out_error=sum(a != b for a, b in zip(actual, expected)) / len(expected),
                )
            except Exception as exc:
                record.update(status="failed", error=f"{type(exc).__name__}: {exc}")
            results.append(record)
    output = {
        "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip(),
        "dirty": bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=root, text=True).strip()),
        "protocol": "Same base grammar, lambda=0.05, 4 rounds x 8 proposals, depth=3, seed and wall budget; no tuning",
        "results": results,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + "\n")
    print(args.output)


if __name__ == "__main__":
    main()
