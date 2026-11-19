"""Compare indexed and chunk-wise reverse traversal on identical checked programs."""

from __future__ import annotations

import argparse
from collections.abc import MutableSequence
import gc
import hashlib
from importlib.metadata import version
import json
from pathlib import Path
import platform
import statistics
import subprocess
import sys
from time import perf_counter

from loguru import logger

from aeon.core.types import t_int
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import TypingContext, _ContextSnapshot
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name, fresh_counter
from aeon.verification import smt
from aeon.verification.state import VerificationState


ROOT = Path(__file__).resolve().parents[1]


def sources() -> dict[str, str]:
    element = "{v:Int|v>=5 && v<=10}"
    linked = f"(List.nil{{{element}}})"
    for i in range(20):
        linked = f"(List.cons{{{element}}} {5 + i % 6} {linked})"
    selected = ["true" if i in {2, 3, 4, 5, 6, 12, 13} else "false" for i in range(50)]
    chunks = [
        f"(Array.mk_{size} {' '.join(selected[start : start + size])})" for start, size in [(0, 32), (32, 16), (48, 2)]
    ]
    knapsack = f"Array.mk_concat (Array.mk_concat {chunks[0]} {chunks[1]}) {chunks[2]}"
    return {
        "list_20_bounded": f"import List; def result:{{xs:(List {{v:Int|v>=5 && v<=10}})|List.size xs=20}} := {linked};",
        "array_int_fit": (ROOT / "examples/synthesis/ortools/array_int.ae")
        .read_text()
        .replace("?h", "Array.mk_concat (Array.mk_2 3 (0-7)) (Array.mk_1 10)"),
        "image_key": (ROOT / "examples/image/key.ae").read_text().replace("?hole", "Image.mk target_w target_h white"),
        "knapsack_50": (ROOT / "examples/synthesis/puzzle/knapsack_50.ae").read_text().replace("?solution", knapsack),
    }


def summarize(trials: list[dict]) -> dict:
    medians = {
        variant: statistics.median(t["seconds"] for t in trials if t["variant"] == variant)
        for variant in ("indexed", "chunks")
    }
    return {"trials": trials, "median_seconds": medians, "speedup": medians["indexed"] / medians["chunks"]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repeats", type=int, default=6)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--case", choices=list(sources()))
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("--repeats must be positive")
    logger.remove()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    variants = {"indexed": MutableSequence.__reversed__, "chunks": _ContextSnapshot.__reversed__}
    report: dict = {
        "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "python": sys.version,
        "platform": platform.platform(),
        "z3": version("z3-solver"),
        "protocol": "Same compiled AST and context; alternate variant order; clear SMT caches, reset fresh names and collect garbage before each check. GC stays enabled during timing. Parsing, synthesis, objectives, runtime requirements and preparatory collection are excluded.",
        "repeats": args.repeats,
        "cases": {},
    }
    try:
        for case, source in sources().items():
            if args.case and args.case != case:
                continue
            driver = AeonDriver(AeonConfig("tdsyn_enumerative", SilentSynthesisUI(), 1, check_only=True, no_main=True))
            path = args.output.parent / f"{case}.ae"
            path.write_text(source)
            errors = list(driver.parse(filename=str(path), aeon_code=source))
            assert not errors, (case, [type(error).__name__ for error in errors])
            assert driver.core is not None and driver.typing_ctx is not None
            trials = []
            with driver.session.activate():
                counter_start = fresh_counter.counter + 1000
                for repeat in range(args.repeats):
                    order = ("indexed", "chunks") if repeat % 2 == 0 else ("chunks", "indexed")
                    for variant in order:
                        setattr(_ContextSnapshot, "__reversed__", variants[variant])
                        smt.clear_smt_caches()
                        fresh_counter.counter = counter_start
                        uncertain = driver.session.state(VerificationState).inconclusive_queries
                        gc.collect()
                        started = perf_counter()
                        valid = check_type(driver.typing_ctx, driver.core)
                        elapsed = perf_counter() - started
                        assert valid, (case, variant)
                        assert driver.session.state(VerificationState).inconclusive_queries == uncertain
                        trials.append({"repeat": repeat, "variant": variant, "seconds": elapsed, "valid": valid})
                        print(case, repeat, variant, round(elapsed, 4), file=sys.stderr, flush=True)
            report["cases"][case] = {"source_sha256": hashlib.sha256(source.encode()).hexdigest(), **summarize(trials)}
            args.output.write_text(json.dumps(report, indent=2) + "\n")

        ctx = TypingContext()
        for i in range(256):
            ctx = ctx.with_var(Name("x", i), t_int)
        trials = []
        for repeat in range(args.repeats):
            for variant in ("indexed", "chunks") if repeat % 2 == 0 else ("chunks", "indexed"):
                setattr(_ContextSnapshot, "__reversed__", variants[variant])
                started = perf_counter()
                for _ in range(2000):
                    for _entry in reversed(ctx.entries):
                        pass
                trials.append({"repeat": repeat, "variant": variant, "seconds": perf_counter() - started})
        report["reverse_traversal_256_binders"] = summarize(trials)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(report, indent=2))
    finally:
        setattr(_ContextSnapshot, "__reversed__", variants["chunks"])


if __name__ == "__main__":
    main()
