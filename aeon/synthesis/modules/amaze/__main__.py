"""Offline package-stdlib training. No alternate training corpus is accepted."""

from __future__ import annotations

import argparse
from dataclasses import asdict
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

import psutil

from .learning import Config, train
from .profile import load, save
from .resources import TrainingMemoryLimitExceeded, apply_worker_limits, wait_for_training


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
    worker.add_argument("--display-output", type=Path, help=argparse.SUPPRESS)
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
        try:
            config = Config(**json.loads(args.config))
            apply_worker_limits(config.budget)
            report = train(config)
            save(args.output, report)
            profile = load(args.output)
            print(
                json.dumps(
                    {
                        "profile": str(args.display_output or args.output),
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
    output = args.output.resolve()
    try:
        output.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix=".amaze-", dir=output.parent) as staging:
            staged_output = Path(staging) / "profile.json"
            command = [
                sys.executable,
                "-m",
                "aeon.synthesis.modules.amaze",
                "_train-worker",
                json.dumps(asdict(config)),
                str(staged_output),
                "--display-output",
                str(output),
            ]
            process = subprocess.Popen(command, start_new_session=(os.name == "posix"))
            code = wait_for_training(process, config.budget + 10)
            if code < 0:
                parser.exit(2, f"AMaze offline worker terminated by signal {-code}; no new profile was committed\n")
            if code == 0:
                load(staged_output)
                staged_output.replace(output)
            return code
    except subprocess.TimeoutExpired:
        parser.exit(2, "AMaze offline wall-clock limit exhausted; no new profile was committed\n")
    except TrainingMemoryLimitExceeded as exc:
        parser.exit(2, f"{exc}; no new profile was committed\n")
    except psutil.Error as exc:
        parser.exit(2, f"AMaze offline resource monitoring failed: {exc}; no new profile was committed\n")
    except (OSError, ValueError) as exc:
        parser.exit(2, f"AMaze offline training failed: {exc}; no new profile was committed\n")


if __name__ == "__main__":
    raise SystemExit(main())
