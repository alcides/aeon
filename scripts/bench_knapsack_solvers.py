"""Run the fixed 50-item knapsack in isolated processes and check returned masks.

Run from the checkout to measure, including when comparing older revisions:
python scripts/bench_knapsack_solvers.py --output /tmp/knapsack-results
"""

import argparse
import json
import os
import pathlib
import re
import signal
import subprocess
import sys
import time
import traceback

BACKENDS = [
    "ortools",
    "tdsyn_backward",
    "tdsyn_enumerative",
    "tdsyn_random",
    "gp",
    "random_search",
    "enumerative",
    "synquid",
    "rl_mcts",
    "noisy",
]
p = argparse.ArgumentParser()
p.add_argument("--child")
p.add_argument("--budget", type=int, default=60)
p.add_argument("--wall-limit", type=int, default=180)
p.add_argument("--output", required=True)
p.add_argument("--backends", nargs="+", choices=BACKENDS, default=BACKENDS)
a = p.parse_args()
if a.budget <= 0 or a.wall_limit <= 5:
    p.error("budget must be positive and wall-limit must exceed 5 seconds")
out = pathlib.Path(a.output).resolve()
out.mkdir(parents=True, exist_ok=True)
root = pathlib.Path.cwd()
example = "examples/synthesis/puzzle/knapsack_50.ae"

if a.child:
    sys.path.insert(0, str(root))
    sys.setrecursionlimit(10000)
    import faulthandler

    faulthandler.dump_traceback_later(a.wall_limit - 5)
    from loguru import logger

    logger.remove()
    from aeon.facade.driver import AeonConfig, AeonDriver
    from aeon.synthesis.uis.api import SilentSynthesisUI
    from aeon.synthesis.api import UnsupportedSynthesisGoal, SynthesisNotSuccessful

    started = time.monotonic()
    result = {"backend": a.child, "budget_seconds": a.budget}

    class UI(SilentSynthesisUI):
        synthesis_start: float | None = None

        def note(self):
            if self.synthesis_start is not None and "first_solution_seconds" not in result:
                result["first_solution_seconds"] = round(time.monotonic() - self.synthesis_start, 3)
                (out / (a.child + ".progress.json")).write_text(json.dumps(result, indent=2))

        def register(self, solution, quality, elapsed_time, is_best):
            if solution is not None and isinstance(quality, list):
                self.note()

        def register_front(self, front, elapsed_time):
            if front:
                self.note()

        def display_results(self, *args, **kwargs):
            pass

    ui = UI()
    try:
        driver = AeonDriver(AeonConfig(a.child, ui, a.budget, strict_decidable=True))
        errors = list(driver.parse(filename=example))
        if errors:
            raise RuntimeError(str(errors))
        result["parse_seconds"] = round(time.monotonic() - started, 3)
        assert driver.has_synth()
        ui.synthesis_start = time.monotonic()
        driver.synth()
        result["synthesis_seconds"] = round(time.monotonic() - ui.synthesis_start, 3)
        value = driver.run()
        decisions = []
        while isinstance(value, tuple) and value[0] == "Mask_cons":
            _, value, used = value
            assert type(used) is bool
            decisions.append(used)
        assert value == ("Mask_empty",) and len(decisions) == 50
        data = pathlib.Path("examples/synthesis/puzzle/knapsack_data.ae").read_text()

        def column(name):
            match = re.search(r"def " + name + r"\b.*?#\[(.*?)\]", data, re.S)
            assert match is not None
            return list(map(int, re.findall(r"\d+", match.group(1))))

        weights, values = column("weights"), column("values")
        assert len(weights) == len(values) == 50
        weight = sum(w for w, used in zip(weights, decisions) if used)
        total = sum(v for v, used in zip(values, decisions) if used)
        assert weight <= 100
        result.update(status="solved", decisions=decisions, selected=sum(decisions), weight=weight, value=total)
    except UnsupportedSynthesisGoal as e:
        result.update(status="unsupported", detail=str(e))
    except SynthesisNotSuccessful as e:
        result.update(status="no_solution", detail=str(e))
    except Exception as e:
        result.update(status="error", detail=type(e).__name__ + ": " + str(e))
        traceback.print_exc()
    result["wall_seconds"] = round(time.monotonic() - started, 3)
    faulthandler.cancel_dump_traceback_later()
    (out / (a.child + ".json")).write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result), flush=True)
else:
    report = {
        "example": example,
        "budget_seconds": a.budget,
        "wall_limit_seconds": a.wall_limit,
        "seed": 0,
        "python_hash_seed": 0,
        "results": [],
    }
    for backend in a.backends:
        start = time.monotonic()
        print("START", backend, flush=True)
        # Never report a previous run's result when this process times out.
        (out / (backend + ".json")).unlink(missing_ok=True)
        (out / (backend + ".progress.json")).unlink(missing_ok=True)
        command = [
            sys.executable,
            __file__,
            "--child",
            backend,
            "--budget",
            str(a.budget),
            "--wall-limit",
            str(a.wall_limit),
            "--output",
            str(out),
        ]
        with (out / (backend + ".log")).open("w") as log:
            proc = subprocess.Popen(
                command,
                cwd=root,
                env={**os.environ, "AEON_SEED": "0", "PYTHONHASHSEED": "0"},
                stdout=log,
                stderr=subprocess.STDOUT,
                start_new_session=True,
            )
            try:
                code = proc.wait(timeout=a.wall_limit)
                file = out / (backend + ".json")
                result = (
                    json.loads(file.read_text())
                    if file.exists()
                    else {"backend": backend, "status": "error", "exit_code": code}
                )
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGTERM)
                try:
                    proc.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid, signal.SIGKILL)
                    proc.wait()
                result = {
                    "backend": backend,
                    "status": "wall_timeout",
                    "wall_seconds": round(time.monotonic() - start, 3),
                }
                progress = out / (backend + ".progress.json")
                if progress.exists():
                    result.update(json.loads(progress.read_text()))
        report["results"].append(result)
        (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps({k: v for k, v in result.items() if k != "decisions"}), flush=True)
