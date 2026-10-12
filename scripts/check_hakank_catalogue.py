"""Compile catalogue ports in isolated subprocesses with bounded wall time.

A passing compilation is recorded separately from independent solution
validation. Timeouts are not reported as invalid or infeasible models.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import sys


CHECK = """
import json, sys
from pathlib import Path
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI
configuration = AeonConfig(synthesizer="ortools", synthesis_ui=SilentSynthesisUI(), synthesis_budget=1)
driver = AeonDriver(configuration)
errors = driver.parse(aeon_code=Path(sys.argv[1]).read_text())
print("HAKANK_RESULT " + json.dumps([str(error) for error in errors]))
raise SystemExit(bool(errors))
"""


def check_catalogue(catalogue, output, identifiers, timeout, workers, limit):
    root = catalogue.parent
    data = json.loads(catalogue.read_text())
    selected = [
        entry for entry in data["models"] if entry.get("aeon_file") and (not identifiers or entry["id"] in identifiers)
    ]
    if limit:
        selected = selected[:limit]
    library = Path(__file__).resolve().parents[1] / "aeon/libraries/Vec.ae"
    results = []

    def check(entry):
        file = root / entry["aeon_file"]
        result = dict(
            id=entry["id"],
            aeon_sha256=hashlib.sha256(file.read_bytes()).hexdigest(),
            library_sha256=hashlib.sha256(library.read_bytes()).hexdigest(),
        )
        try:
            process = subprocess.run(
                [sys.executable, "-c", CHECK, str(file.resolve())], capture_output=True, text=True, timeout=timeout
            )
            result["status"] = "typechecked" if process.returncode == 0 else "error"
            if process.returncode:
                result["error"] = (process.stdout + process.stderr)[-4000:]
        except subprocess.TimeoutExpired:
            result.update(status="timeout", timeout_seconds=timeout)
        return result

    with ThreadPoolExecutor(max_workers=workers) as pool:
        for result in pool.map(check, selected):
            results.append(result)
            output.write_text(json.dumps(results, indent=2) + "\n")
            print(result["id"], result["status"], flush=True)
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--catalogue", type=Path, default=Path("examples/synthesis/hakank/catalogue.json"))
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--ids", default="")
    parser.add_argument("--timeout", type=float, default=60)
    parser.add_argument("--workers", type=int, default=2)
    parser.add_argument("--limit", type=int, default=0)
    args = parser.parse_args()
    check_catalogue(
        args.catalogue,
        args.output,
        set(args.ids.split(",")) if args.ids else set(),
        args.timeout,
        args.workers,
        args.limit,
    )


if __name__ == "__main__":
    main()
