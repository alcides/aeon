"""Isolated, resumable runs of the same Aeon tasks through any backend."""

from __future__ import annotations

from collections import Counter
from dataclasses import asdict
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import re
from typing import Any

from aeon.benchmarks.bounded_boolean.corpus import ROOT, ae_name, digest, emit, load_case


IMPLEMENTATION = Path(__file__).resolve().parents[3]


def candidate_digest(outputs) -> str:
    return digest(json.dumps(outputs, sort_keys=True).encode())


def completed_source(source: str, outputs: dict, circuit) -> str:
    bodies = {}
    for name, clauses in outputs.items():
        parts = []
        for clause in clauses:
            literals = [("!" if v < 0 else "") + ae_name(circuit.x[abs(v) - 1]) for v in clause]
            parts.append("(" + " || ".join(literals) + ")" if literals else "false")
        bodies[f"hole_{ae_name(name)}"] = "(" + " && ".join(parts) + ")" if parts else "true"
    return re.sub(r"\?([A-Za-z_][A-Za-z_0-9]*)", lambda match: bodies[match[1]], source)


def write_json(path: Path, value) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n")
    temporary.replace(path)


def identity() -> dict:
    revision = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=IMPLEMENTATION, text=True, capture_output=True, check=False
    ).stdout.strip()
    # Include uncommitted implementation files in the identity, not generated
    # results. A coverage report can therefore record an honest pre-commit run.
    payload = b"".join(
        p.relative_to(IMPLEMENTATION).as_posix().encode() + b"\0" + p.read_bytes()
        for p in sorted((IMPLEMENTATION / "aeon").rglob("*.py"))
    )
    return {"aeon_revision": revision, "implementation_sha256": digest(payload), "python": sys.version.split()[0]}


def worker(request: dict, destination: Path) -> None:
    from loguru import logger

    logger.remove()
    from aeon.benchmarks.bounded_boolean.checker import CheckFailure, check, check_import, extract, exhaustive_status
    from aeon.core.substitutions import substitution
    from aeon.core.types import top
    from aeon.facade.driver import AeonConfig, AeonDriver
    from aeon.synthesis.api import SynthesisNotSuccessful, TimeoutInEvaluationException, UnsupportedSynthesisGoal
    from aeon.synthesis.entrypoint import synthesize_holes
    from aeon.synthesis.identification import incomplete_functions_and_holes, term_has_holes
    from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
    from aeon.synthesis.uis.api import SilentSynthesisUI
    from aeon.typechecking.typeinfer import check_type

    start = time.monotonic()
    result: dict[str, Any] = {"status": "running", "phase": "parse", "timings": {}}
    backend = None
    phase_start = start

    def phase(name):
        nonlocal phase_start
        now = time.monotonic()
        result["timings"][result["phase"]] = now - phase_start
        phase_start = now
        result["phase"] = name
        write_json(destination, result)

    try:
        write_json(destination, result)
        os.environ["AEON_SEED"] = str(request["seed"])
        root = Path(request["root"])
        circuit = load_case(request["case"], root)
        driver = AeonDriver(AeonConfig(request["backend"], SilentSynthesisUI(), request["budget"], no_main=True))
        errors = list(driver.parse(filename=request["source_path"], aeon_code=request["source"]))
        if errors:
            raise CheckFailure("translation_failure", "; ".join(map(str, errors)))
        phase("import_verification")
        result["import_check"] = check_import(driver.core, circuit)
        if result["import_check"] != "equivalent":
            raise CheckFailure(result["import_check"], "generated relation could not be proved equivalent")
        if request["audit"]:
            result["status"] = "import_verified"
        else:
            phase("synthesis")
            backend = make_synthesizer(request["backend"])
            with driver.session.activate():
                targets = incomplete_functions_and_holes(driver.typing_ctx, driver.core)
                mapping = synthesize_holes(
                    driver.typing_ctx,
                    driver.evaluation_ctx,
                    driver.core,
                    targets,
                    driver.metadata,
                    backend,
                    request["budget"],
                    SilentSynthesisUI(),
                )
                if not mapping or any(value is None for value in mapping.values()):
                    raise CheckFailure("no_solution", "backend returned no complete candidate")
                phase("verification")
                completed = driver.core
                for name, value in mapping.items():
                    completed = substitution(completed, value, name)
                if term_has_holes(completed) or not check_type(driver.typing_ctx, completed, top):
                    raise CheckFailure("type_failure", "completed program failed Aeon validation")
                outputs = extract(completed, circuit, request["bound"])
                result.update(check(circuit, outputs, request["bound"]))
                result["outputs"] = outputs
                result["candidate_sha256"] = candidate_digest(outputs)
    except UnsupportedSynthesisGoal as exc:
        result.update(status="unsupported", reason=str(exc))
    except TimeoutInEvaluationException as exc:
        result.update(status="timeout", reason=str(exc))
    except CheckFailure as exc:
        result.update(status=exc.status, reason=str(exc))
    except SynthesisNotSuccessful as exc:
        status = getattr(exc, "category", "search_failed")
        result.update(status=status, reason=str(exc))
        if status == "bounded_unsat":
            oracle = exhaustive_status(circuit, request["bound"])
            result["certification"] = (
                "exhaustive" if oracle == "bounded_unsat" else "solver_reported_not_independently_certified"
            )
            if oracle == "feasible":
                result.update(status="validation_error", reason="bounded UNSAT disagrees with independent enumeration")
    except ImportError as exc:
        result.update(status="unavailable", reason=str(exc))
    except MemoryError:
        result.update(status="resource_limit", reason="worker memory exhausted")
    except Exception as exc:
        result.update(status="internal_error", reason=f"{type(exc).__name__}: {exc}")
    finally:
        result["timings"][result["phase"]] = time.monotonic() - phase_start
        result["timings"]["worker_total"] = time.monotonic() - start
        if backend is not None and hasattr(backend, "report"):
            result["backend_report"] = asdict(backend.report)
        write_json(destination, result)


def terminate(process) -> None:
    if os.name == "posix":
        # Fitness pools inherit the worker's process group and must die too.
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    else:
        process.kill()
    process.wait()


def run_one(
    case: dict,
    backend: str,
    output: Path,
    *,
    bound: int = 5,
    budget: float = 5,
    wall_timeout: float = 35,
    seed: int = 0,
    root: Path = ROOT,
    audit: bool = False,
    resume: bool = True,
    provenance: dict | None = None,
    memory_mb: int = 4096,
) -> dict:
    circuit = load_case(case, root)
    source = emit(circuit, case["id"], bound)
    config = {
        "task": case["id"],
        "backend": backend,
        "bound": bound,
        "budget": budget,
        "wall_timeout": wall_timeout,
        "memory_mb": memory_mb,
        "seed": seed,
        "audit": audit,
        "input_count": len(circuit.x),
        "output_count": len(circuit.y),
        "source_sha256": digest(source.encode()),
        "verilog_sha256": digest((root / "upstream" / case["source"]).read_bytes()),
        "y_sha256": digest((root / "upstream" / case["y_file"]).read_bytes()),
        **(provenance or identity()),
    }
    key = digest(json.dumps(config, sort_keys=True).encode())
    output.mkdir(parents=True, exist_ok=True)
    final = output / f"{key}.json"
    if resume and final.exists():
        saved = json.loads(final.read_text())
        if (
            saved.get("key") == key
            and saved.get("config") == config
            and ("outputs" not in saved or saved.get("candidate_sha256") == candidate_digest(saved["outputs"]))
        ):
            return saved
    source_path = output / f"{key}.ae"
    source_path.write_text(source)
    request = config | {
        "case": case,
        "root": str(root.resolve()),
        "source": source,
        "source_path": str(source_path.resolve()),
    }
    request_path, progress = output / f"{key}.request.json", output / f"{key}.progress.json"
    write_json(request_path, request)
    progress.unlink(missing_ok=True)
    start = time.monotonic()
    command = [
        sys.executable,
        "-m",
        "aeon.benchmarks.bounded_boolean",
        "_worker",
        str(request_path.resolve()),
        str(progress.resolve()),
    ]
    with (output / f"{key}.log").open("w") as log:
        env = os.environ | {
            "PYTHONPATH": str(IMPLEMENTATION),
            "AEON_SEED": str(seed),
            "OPENBLAS_NUM_THREADS": "1",
            "OMP_NUM_THREADS": "1",
        }
        process = subprocess.Popen(
            command, cwd=IMPLEMENTATION, env=env, stdout=log, stderr=log, start_new_session=(os.name == "posix")
        )
        timed_out = False
        try:
            process.wait(timeout=wall_timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            terminate(process)
        finally:
            # Also reap any fitness descendants left after a worker failure.
            if os.name == "posix":
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
    result = json.loads(progress.read_text()) if progress.exists() else {}
    if timed_out:
        result.update(status="timeout", reason="isolated wall-clock limit exceeded")
    elif process.returncode != 0 or result.get("status") in {None, "running"}:
        resource_signal = process.returncode in {-signal.SIGKILL, -getattr(signal, "SIGXCPU", signal.SIGKILL)}
        result.update(
            status="resource_limit" if resource_signal else "worker_failure",
            reason=f"worker exited {process.returncode}",
        )
    result.setdefault("timings", {})["total"] = time.monotonic() - start
    result.update(key=key, config=config, source_file=source_path.name)
    if "outputs" in result:
        candidate_file = output / f"{key}.candidate.ae"
        candidate_file.write_text(completed_source(source, result["outputs"], circuit))
        result["candidate_file"] = candidate_file.name
    write_json(final, result)
    request_path.unlink(missing_ok=True)
    progress.unlink(missing_ok=True)
    return result


def summary(results: list[dict]) -> dict:
    return {
        "attempted": len(results),
        "statuses": dict(sorted(Counter(r["status"] for r in results).items())),
        "by_backend": {
            backend: dict(Counter(r["status"] for r in results if r["config"]["backend"] == backend))
            for backend in sorted({r["config"]["backend"] for r in results})
        },
    }
