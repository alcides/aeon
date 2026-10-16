#!/usr/bin/env python3
"""Standard-library experiment planner, isolated runner and result collector."""

import argparse
import collections
from concurrent.futures import ThreadPoolExecutor
import csv
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import platform
import re
import shlex
import shutil
import signal
import socket
import statistics
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


_STORAGE_TOOLS = None


def storage_tools():
    global _STORAGE_TOOLS
    if _STORAGE_TOOLS is not None:
        return _STORAGE_TOOLS
    current_file = ROOT / "source/current.json"
    current = read_json(current_file) if current_file.exists() else {"path": "source/aeon"}
    candidates = [
        ROOT / current["path"] / "aeon/benchmarks/resources.py",
        ROOT / "aeon-psb2-github/aeon/benchmarks/resources.py",
        ROOT.parents[1] / "aeon/benchmarks/resources.py",
    ]
    for path in candidates:
        if path.exists():
            spec = importlib.util.spec_from_file_location("_aeon_evaluation_resources", path)
            module = importlib.util.module_from_spec(spec)
            sys.modules[spec.name] = module
            spec.loader.exec_module(module)
            _STORAGE_TOOLS = module
            return module
    raise RuntimeError("Repository-owned benchmark storage safeguards are unavailable")


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, default=str) + "\n")
    temporary.replace(path)


def read_json(path):
    return json.loads(Path(path).read_text())


def source_digest(source):
    digest = hashlib.sha256()
    for p in sorted(source.rglob("*")):
        if p.is_file() and "__pycache__" not in p.parts and p.suffix != ".pyc":
            digest.update(str(p.relative_to(source)).encode())
            digest.update(p.read_bytes())
    return digest.hexdigest()


def snapshot(args):
    source = Path(args.source).resolve()
    destination = ROOT / "source" / "aeon"
    if destination.exists():
        raise SystemExit("Snapshot already exists; use a new experiment folder to refresh it.")
    paths = subprocess.check_output(
        ["git", "-C", str(source), "ls-files", "-z", "--cached", "--others", "--exclude-standard"]
    ).split(b"\0")
    for raw in paths:
        if not raw:
            continue
        rel = Path(os.fsdecode(raw))
        if rel.parts[0] in ("artifacts", "target"):
            continue
        src = source / rel
        if src.is_file():
            dst = destination / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, dst)
    if (source / "uv.lock").is_file():
        shutil.copy2(source / "uv.lock", destination / "uv.lock")
    # Capture ignored external data too, when already materialized.
    cache = source / "benchmarks/vericoding/.cache"
    if cache.exists():
        shutil.copytree(cache, destination / "benchmarks/vericoding/.cache", dirs_exist_ok=True)
    write_json(
        ROOT / "source/provenance.json",
        {
            "origin": str(source),
            "commit": subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip(),
            "git_status": subprocess.check_output(["git", "-C", str(source), "status", "--porcelain"], text=True),
            "snapshot_sha256": source_digest(destination),
            "created_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        },
    )
    (ROOT / "source/local-changes.patch").write_bytes(
        subprocess.check_output(["git", "-C", str(source), "diff", "HEAD", "--binary"])
    )
    print(destination)


def features(path, source):
    text = path.read_text(errors="replace")
    # Lexical features, not a substitute for compiler-derived goal telemetry.
    clean = re.sub(r'"(?:\\.|[^"\\])*"|#[^\n]*|//[^\n]*|/\*.*?\*/', " ", text, flags=re.S)
    holes = sorted(set(re.findall(r"\?([A-Za-z_][\w]*)", clean)))
    inventory_error = None
    try:
        from aeon.benchmarks.inventory import term_hole_names
    except ModuleNotFoundError as exc:
        if exc.name != "aeon.benchmarks.inventory":
            raise
        # Preserve legacy snapshot replay; new sources provide the AST inventory.
    else:
        try:
            holes = list(term_hole_names(text, str(path)))
        except Exception as exc:
            # Retain malformed files and their lexical candidates in the audit.
            inventory_error = f"{type(exc).__name__}: {exc}"
    rel = str(path.relative_to(source))
    return {
        "case": rel,
        "suite": "/".join(Path(rel).parts[:-1]),
        "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "hole_inventory_error": inventory_error,
        "bytes": path.stat().st_size,
        "lines": len(text.splitlines()),
        "holes": len(holes),
        "hole_names": holes,
        "definitions": len(re.findall(r"\bdef\b", clean)),
        "imports": re.findall(r"\bimport\s+([\w.]+)", clean),
        "decorators": re.findall(r"@([\w]+)", clean),
        "examples": len(re.findall(r"@example\b", clean)),
        "properties": len(re.findall(r"@(?:assert_property|assert_properties|property)\b", clean)),
        "refinements": len(re.findall(r"\{[^{}]*\|", clean)),
        "branches": len(re.findall(r"\bif\b", clean)),
        "matches": len(re.findall(r"\bmatch\b", clean)),
        "adts": len(re.findall(r"\b(?:type|data)\b", clean)),
        "uses_int": bool(re.search(r"\bInt\b", clean)),
        "uses_float": bool(re.search(r"\bFloat\b", clean)),
        "uses_string": bool(re.search(r"\bString\b", clean)),
        "uses_list": bool(re.search(r"\bList\b", clean)),
        "uses_modulo": "%" in clean,
        "uses_disjunction": "||" in clean,
        "external_data": bool(re.search(r"@csv_file|\.csv|\.png|\.npy|\.parquet|\.json", clean)),
        "fitness": bool(re.search(r"@(?:multi_)?(?:minimize|maximize)|@assert_propert", clean)),
    }


def inventory(source):
    return [
        features(p, source) for folder in ("examples", "benchmarks") for p in sorted((source / folder).rglob("*.ae"))
    ]


def materialize(args):
    source = ROOT / "source/aeon"
    sys.path.insert(0, str(source / "benchmarks/vericoding"))
    import run as vericoding

    tasks = [
        line.strip()
        for line in vericoding.TASK_LIST.read_text().splitlines()
        if line.strip() and not line.startswith("#")
    ]
    results = []
    for task in tasks:
        try:
            path = vericoding.translate_to_file(task)
            results.append({"task": task, "status": "translated", "path": str(path.relative_to(source))})
        except vericoding.TranslationError as e:
            results.append({"task": task, "status": "rejected", "reason": str(e)})
        except Exception as e:
            results.append({"task": task, "status": "fetch_or_translation_error", "reason": str(e)})
        print(task, results[-1]["status"], flush=True)
    write_json(ROOT / "source/vericoding-coverage.json", results)
    provenance = read_json(ROOT / "source/provenance.json")
    provenance["snapshot_sha256"] = source_digest(source)
    write_json(ROOT / "source/provenance.json", provenance)


def plan(args):
    config = read_json(args.config)
    if config["budget_s"] <= 0 or config["grace_s"] < 0 or not config["seeds"]:
        raise SystemExit("Budget must be positive; grace nonnegative; at least one seed is required.")
    if len(set(config["seeds"])) != len(config["seeds"]):
        raise SystemExit("Seeds must be unique")
    run = Path(args.run).resolve()
    if run.exists():
        raise SystemExit("Run directory exists; choose a new name to preserve old results.")
    source = Path(args.source).resolve()
    sys.path.insert(0, str(source))
    cases = inventory(source)
    by_name = {x["case"]: x for x in cases}
    selected = (
        [x for x in cases if x["holes"]] if config["cases"] == "all_holes" else [by_name[x] for x in config["cases"]]
    )
    selected = [x for x in selected if x["holes"] > 0]
    aliases = {"tdsyn": "tdsyn_enumerative", "xfta": "symetric", "ortools_int": "ortools", "cpsat": "ortools"}
    sys.path.insert(0, str(source))
    from aeon.synthesis.modules.synthesizerfactory import SYNTHESIZER_LABELS, SYNTHESIZER_FAMILIES, validate_synthesizer

    algorithms = list(dict.fromkeys(aliases.get(x, x) for x in config["algorithms"]))
    for algorithm in algorithms:
        validate_synthesizer(algorithm)
    registry = [
        {
            "algorithm": x,
            "label": label,
            "family": SYNTHESIZER_FAMILIES[x].value,
            "selected": x in algorithms,
            "alias_of": aliases.get(x),
            "exclusion": None
            if x in algorithms
            else (
                "alias"
                if x in aliases
                else "LLM requires service/model"
                if x.startswith("llm")
                else "single-step demonstration backend"
            ),
        }
        for x, label in SYNTHESIZER_LABELS.items()
    ]
    jobs = []
    for case in selected:
        for algorithm in algorithms:
            for seed in config["seeds"]:
                jobs.append(
                    {
                        "id": len(jobs),
                        "case": case["case"],
                        "algorithm": algorithm,
                        "seed": seed,
                        "budget_s": config["budget_s"],
                        "timeout_s": config.get(
                            "timeout_s", config["budget_s"] * max(1, case["holes"]) + config["grace_s"]
                        ),
                    }
                )
    if config.get("psb2_samples"):
        samples = ROOT / config["psb2_samples"]
        config["psb2_manifest_sha256"] = hashlib.sha256((samples / "manifest.json").read_bytes()).hexdigest()
    if not jobs:
        raise SystemExit("Empty plan")
    run.mkdir(parents=True)
    (run / "results").mkdir()
    (run / "logs").mkdir()
    write_json(run / "all-files-inventory.json", cases)
    write_json(run / "inventory.json", selected)
    (run / "programs.txt").write_text("\n".join(x["case"] for x in selected) + "\n")
    write_json(run / "algorithms.json", registry)
    provenance_file = source.with_name(source.name + ".provenance.json")
    if not provenance_file.exists():
        provenance_file = ROOT / "source/provenance.json"
    write_json(
        run / "plan.json",
        {
            "config": config,
            "source": str(source),
            "source_sha256": source_digest(source),
            "provenance": read_json(provenance_file),
            "jobs": jobs,
        },
    )
    with (run / "features.csv").open("w") as f:
        writer = csv.DictWriter(f, fieldnames=list(cases[0]))
        writer.writeheader()
        writer.writerows(selected)
    print(
        f"{len(cases)} inventoried; {len(selected)} selected; {len(jobs)} jobs; upper bound {sum(x['timeout_s'] for x in jobs) / 3600:.2f} CPU hours"
    )


def parse_holes(stdout):
    marker = "Synthesized holes:"
    if marker not in stdout:
        return {}
    try:
        value, _ = json.JSONDecoder().raw_decode(stdout.split(marker)[-1].lstrip())
        return value if isinstance(value, dict) else {}
    except ValueError:
        return {}


def execute(run, job, python):
    plan_data = read_json(run / "plan.json")
    source = Path(plan_data["source"])
    prefix = run / "results" / f"{job['id']:07d}"
    result_file = prefix.with_suffix(".json")
    if result_file.exists():
        return
    # Concurrent duplicate submissions fail instead of corrupting a result.
    lock = prefix.with_suffix(".lock")
    fd = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
    os.close(fd)
    env = os.environ.copy()
    env.update(
        AEON_SOURCE=str(source),
        AEON_EVENTS=str(prefix.with_suffix(".events.jsonl")),
        AEON_SEED=str(job["seed"]),
        PYTHONHASHSEED=str(job["seed"]),
        OMP_NUM_THREADS="1",
        OPENBLAS_NUM_THREADS="1",
        MKL_NUM_THREADS="1",
        NUMEXPR_NUM_THREADS="1",
    )
    if plan_data.get("config", {}).get("psb2_samples"):
        samples = ROOT / plan_data["config"]["psb2_samples"]
        checksum = hashlib.sha256((samples / "manifest.json").read_bytes()).hexdigest()
        if checksum != plan_data["config"]["psb2_manifest_sha256"]:
            lock.unlink(missing_ok=True)
            raise RuntimeError("Prepared PSB2 dataset manifest changed")
        env["AEON_PSB2_SAMPLES"] = str(samples)
    if plan_data.get("config", {}).get("compact_telemetry"):
        env.update(AEON_EVENT_FRONT_LIMIT="3", AEON_EVENT_INTERVAL="1", AEON_QUIET_PROGRESS="1")
    command = [
        python,
        str(ROOT / "scripts/worker.py"),
        "--no-main",
        "--budget",
        str(job["budget_s"]),
        "-s",
        job["algorithm"],
        "--synthesis-format",
        "json",
        str(source / job["case"]),
    ]
    start = time.monotonic()
    timed_out = False
    infrastructure_error = None
    tools = storage_tools()
    policy = tools.StoragePolicy()
    metrics = prefix.with_suffix(".resources")
    measured = Path("/usr/bin/time").is_file()
    if measured:
        command = ["/usr/bin/time", "-f", "%U %S %M", "-o", str(metrics), *command]
    command = tools.bounded_command(command, policy)
    try:
        policy.preflight(run)
        with prefix.with_suffix(".stdout").open("w") as stdout, prefix.with_suffix(".stderr").open("w") as stderr:
            process = subprocess.Popen(
                command, cwd=source, env=env, stdout=stdout, stderr=stderr, start_new_session=True
            )
            try:
                tools.wait_with_limits(
                    process,
                    run,
                    [prefix.with_suffix(ext) for ext in (".stdout", ".stderr", ".events.jsonl", ".resources")],
                    job["timeout_s"],
                    policy,
                )
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            except tools.StorageLimitError as exc:
                infrastructure_error = str(exc)
        cpu_s = peak_rss = None
        if metrics.exists():
            try:
                user, system, rss = metrics.read_text().splitlines()[-1].split()
                cpu_s, peak_rss = float(user) + float(system), int(rss)
            except (ValueError, IndexError):
                pass
        output = prefix.with_suffix(".stdout").read_text(errors="replace")
        error = prefix.with_suffix(".stderr").read_text(errors="replace")
        holes = parse_holes(output)
        events_file = prefix.with_suffix(".events.jsonl")
        events = []
        if events_file.exists():
            for line in events_file.read_text().splitlines():
                try:
                    events.append(json.loads(line))
                except ValueError:
                    pass  # An interrupted write is retained in raw telemetry.
        ends = [x for x in events if x["event"] == "end"]
        expected_holes = features(source / job["case"], source)["holes"]
        filled = len(holes) >= expected_holes > 0 and all(
            isinstance(x, str) and x not in ("None", "") and not re.search(r"\?\w+", x) for x in holes.values()
        )
        status = (
            "infrastructure_error"
            if infrastructure_error
            else "timeout"
            if timed_out
            else "filled"
            if process.returncode == 0 and filled
            else "dependency_missing"
            if "ModuleNotFoundError" in error or "requires the optional" in error
            else "no_solution"
            if process.returncode == 2
            else "error"
            if process.returncode != 0
            else "incomplete"
        )
        write_json(
            result_file,
            {
                **job,
                "status": status,
                "elapsed_s": time.monotonic() - start,
                "infrastructure_detail": infrastructure_error,
                "cpu_s": cpu_s,
                "peak_rss_kib": peak_rss,
                "exit_code": process.returncode,
                "holes": holes,
                "final_targets": ends,
                "source_sha256": plan_data["source_sha256"],
                "host": socket.gethostname(),
                "platform": platform.platform(),
                "python": python,
                "slurm_job": env.get("SLURM_JOB_ID"),
                "command": command,
                "error_tail": (error or output)[-2000:] if status != "filled" else None,
                "objective_verified": bool(
                    status == "filled" and ends and all(x.get("objective_verified") is True for x in ends)
                ),
            },
        )
        print(job["id"], job["algorithm"], job["case"], status, flush=True)
    finally:
        if "process" in locals():
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
        lock.unlink(missing_ok=True)


def run_jobs(args):
    run = Path(args.run).resolve()
    plan_data = read_json(run / "plan.json")
    if source_digest(Path(plan_data["source"])) != plan_data["source_sha256"]:
        raise SystemExit("Source changed since plan creation; create a new plan.")
    jobs = plan_data["jobs"]
    if args.index is not None:
        jobs = [jobs[args.index]]
    python = str(Path(args.python).absolute())
    if args.workers < 1:
        raise SystemExit("--workers must be positive")
    if args.workers == 1:
        for job in jobs:
            execute(run, job, python)
    else:
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            list(pool.map(lambda job: execute(run, job, python), jobs))


def collect(args):
    run = Path(args.run).resolve()
    plan_data = read_json(run / "plan.json")
    rows = [read_json(p) for p in sorted((run / "results").glob("*.json"))]
    completed = {r["id"] for r in rows}
    missing = [j["id"] for j in plan_data["jobs"] if j["id"] not in completed]
    feats = {r["case"]: r for r in read_json(run / "inventory.json")}
    with (run / "results.csv").open("w") as f:
        fields = [
            "id",
            "case",
            "algorithm",
            "seed",
            "status",
            "elapsed_s",
            "cpu_s",
            "peak_rss_kib",
            "budget_s",
            "exit_code",
            "hole_count",
            "holes",
            "final_targets",
        ] + [k for k in next(iter(feats.values())) if k not in ("case", "holes")]
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            merged = {**feats[row["case"]], **row, "hole_count": feats[row["case"]]["holes"]}
            writer.writerow({k: merged.get(k) for k in fields})
    groups = collections.defaultdict(list)
    for row in rows:
        groups[row["algorithm"]].append(row)
    lines = [
        f"Completed {len(rows)}/{len(plan_data['jobs'])}; missing {len(missing)}.",
        "",
        "| Algorithm | Filled | Total | Median wall s | Status counts |",
        "|---|---:|---:|---:|---|",
    ]
    for algorithm, values in sorted(groups.items()):
        counts = dict(collections.Counter(x["status"] for x in values))
        lines.append(
            f"| {algorithm} | {counts.get('filled', 0)} | {len(values)} | {statistics.median(x['elapsed_s'] for x in values):.2f} | {counts} |"
        )
    lines += [
        "",
        "Filled means Aeon returned every reported hole with exit code 0. It does not establish that a fitness optimum or every example/property was satisfied.",
        "Wall time includes interpreter startup, compilation and synthesis. Telemetry records search times and goal types separately.",
        "Feature associations are observational; use matched case/seed comparisons and controlled problem variants before claiming causation.",
    ]
    (run / "summary.md").write_text("\n".join(lines) + "\n")
    write_json(run / "missing.json", missing)
    print("\n".join(lines))


def submit(args):
    run = Path(args.run).resolve()
    jobs = read_json(run / "plan.json")["jobs"]
    if args.chunk_size < 1 or args.concurrency < 1:
        raise SystemExit("Chunk size and concurrency must be positive")
    tools = storage_tools()
    tools.StoragePolicy(min_free_bytes=256 * 1024 * 1024).preflight(run, args.concurrency)
    chunks = math.ceil(len(jobs) / args.chunk_size)
    commands = []
    for chunk in range(chunks):
        offset = chunk * args.chunk_size
        count = min(args.chunk_size, len(jobs) - offset)
        wall = max(x["timeout_s"] for x in jobs[offset : offset + count]) + 90
        cmd = [
            "sbatch",
            "--parsable",
            f"--array=0-{count - 1}%{args.concurrency}",
            "--cpus-per-task=1",
            f"--mem={args.mem}",
            f"--time={math.ceil(wall / 60)}",
            "--job-name=aeon-eval",
            f"--output={run}/logs/%A_%a.out",
            f"--error={run}/logs/%A_%a.err",
        ]
        if args.partition:
            cmd += ["--partition", args.partition]
        if args.account:
            cmd += ["--account", args.account]
        if args.dependency:
            cmd += ["--dependency", args.dependency]
        cmd += [str(ROOT / "slurm/array.sbatch"), str(run), str(Path(args.python).absolute()), str(offset)]
        print(shlex.join(cmd), flush=True)
        if not args.dry_run:
            commands.append({"command": cmd, "job_id": subprocess.check_output(cmd, text=True).strip()})
    if commands:
        write_json(run / f"submission-{time.time_ns()}.json", commands)


def main():
    current = ROOT / "source/current.json"
    default_source = ROOT / read_json(current)["path"] if current.exists() else ROOT / "source/aeon"
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    p = sub.add_parser("snapshot")
    p.add_argument("--source", default=str(ROOT.parent / "aeon"))
    p.set_defaults(func=snapshot)
    p = sub.add_parser("materialize-vericoding")
    p.set_defaults(func=materialize)
    p = sub.add_parser("plan")
    p.add_argument("--config", required=True)
    p.add_argument("--run", required=True)
    p.add_argument("--source", default=str(default_source))
    p.set_defaults(func=plan)
    p = sub.add_parser("run")
    p.add_argument("--run", required=True)
    p.add_argument("--index", type=int)
    p.add_argument("--workers", type=int, default=1)
    p.add_argument("--python", default=sys.executable)
    p.set_defaults(func=run_jobs)
    p = sub.add_parser("collect")
    p.add_argument("--run", required=True)
    p.set_defaults(func=collect)
    p = sub.add_parser("submit")
    p.add_argument("--run", required=True)
    p.add_argument("--python", default=sys.executable)
    p.add_argument("--partition")
    p.add_argument("--account")
    p.add_argument("--dependency")
    p.add_argument("--concurrency", type=int, default=8)
    p.add_argument("--chunk-size", type=int, default=500)
    p.add_argument("--mem", default="4G")
    p.add_argument("--dry-run", action="store_true")
    p.set_defaults(func=submit)
    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
