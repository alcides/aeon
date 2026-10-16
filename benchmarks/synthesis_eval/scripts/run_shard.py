#!/usr/bin/env python3
"""Run a resumable partition of a plan, compressing completed raw logs."""

import argparse
import gzip
from pathlib import Path
import shutil

import eval as evaluation


def compress_logs(run, job_id):
    prefix = run / "results" / f"{job_id:07d}"
    for extension in (".stdout", ".stderr", ".events.jsonl", ".resources"):
        path = prefix.with_suffix(extension)
        if not path.exists():
            continue
        destination = Path(str(path) + ".gz")
        temporary = Path(str(destination) + ".tmp")
        try:
            with path.open("rb") as source, gzip.open(temporary, "wb", compresslevel=6) as target:
                shutil.copyfileobj(source, target)
            temporary.replace(destination)
        finally:
            temporary.unlink(missing_ok=True)
        path.unlink()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", required=True)
    parser.add_argument("--python", required=True)
    parser.add_argument("--shard", type=int, required=True)
    parser.add_argument("--shards", type=int, required=True)
    args = parser.parse_args()
    if not 0 <= args.shard < args.shards:
        parser.error("shard must be in [0, shards)")
    run = Path(args.run).resolve()
    plan = evaluation.read_json(run / "plan.json")
    if evaluation.source_digest(Path(plan["source"])) != plan["source_sha256"]:
        raise SystemExit("Source changed since plan creation")
    for job in plan["jobs"]:
        if job["id"] % args.shards != args.shard:
            continue
        tools = evaluation.storage_tools()
        try:
            tools.StoragePolicy(min_free_bytes=256 * 1024 * 1024).preflight(run)
            evaluation.execute(run, job, str(Path(args.python).absolute()))
            compress_logs(run, job["id"])
        except (tools.StorageLimitError, OSError) as exc:
            evaluation.write_json(
                run / f"shard-{args.shard}-infrastructure.json",
                {"status": "infrastructure_error", "trial_id": job["id"], "detail": str(exc)},
            )
            raise SystemExit(str(exc)) from exc


if __name__ == "__main__":
    main()
