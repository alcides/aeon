"""Offline package-stdlib training. No alternate training corpus is accepted."""

from __future__ import annotations

import argparse
from dataclasses import asdict
import json
import math
import os
from pathlib import Path
import subprocess
import sys

from .learning import Config, train
from .profile import load, save


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    trainer = sub.add_parser("train-stdlib")
    trainer.add_argument("--output", type=Path, required=True)
    for name, default in asdict(Config()).items():
        trainer.add_argument("--" + name.replace("_", "-"), type=type(default), default=default)
    worker = sub.add_parser("_train-worker")
    worker.add_argument("config")
    worker.add_argument("output", type=Path)
    inspect = sub.add_parser("inspect")
    inspect.add_argument("profile", type=Path)
    args = parser.parse_args(argv)
    if args.command == "inspect":
        try:
            profile = load(args.profile)
        except ValueError as exc:
            parser.error(str(exc))
        print(
            json.dumps(
                {
                    "sha256": profile.sha256,
                    "stdlib_sha256": profile.stdlib_sha256,
                    "selected_macros": [m.id for m in profile.macros],
                },
                indent=2,
            )
        )
        return 0
    if args.command == "_train-worker":
        from loguru import logger

        logger.remove()
        config = Config(**json.loads(args.config))
        if os.name == "posix":
            import resource

            resource.setrlimit(resource.RLIMIT_AS, (4 * 1024**3, 4 * 1024**3))
            cpu = math.ceil(config.budget) + 5
            resource.setrlimit(resource.RLIMIT_CPU, (cpu, cpu))
        try:
            report = train(config)
            save(args.output, report)
            profile = load(args.output)
            print(
                json.dumps(
                    {
                        "profile": str(args.output),
                        "sha256": profile.sha256,
                        "corpus": report["corpus"]["split_counts"],
                        "selected_macros": len(profile.macros),
                        "offline_seconds": report["offline_seconds"],
                        "held_out": {
                            k: [
                                {x: r[x] for x in ("task", "status", "candidates", "elapsed")}
                                for r in report["held_out"][k]
                            ]
                            for k in ("baseline", "optimized")
                        },
                    },
                    indent=2,
                )
            )
            return 0
        except Exception as exc:
            parser.exit(2, f"AMaze training failed: {exc}\n")
    values = {k: getattr(args, k) for k in asdict(Config())}
    try:
        config = Config(**values)
    except ValueError as exc:
        parser.error(str(exc))
    command = [
        sys.executable,
        "-m",
        "aeon.synthesis.modules.amaze",
        "_train-worker",
        json.dumps(asdict(config)),
        str(args.output.resolve()),
    ]
    process = subprocess.Popen(command, start_new_session=(os.name == "posix"))
    try:
        return process.wait(timeout=config.budget + 10)
    except subprocess.TimeoutExpired:
        if os.name == "posix":
            import signal

            os.killpg(process.pid, signal.SIGKILL)
        else:
            process.kill()
        process.wait()
        parser.exit(2, "AMaze offline wall-clock limit exhausted; no new profile was committed\n")


if __name__ == "__main__":
    raise SystemExit(main())
