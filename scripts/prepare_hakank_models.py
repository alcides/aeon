"""Compile pinned upstream instances for the Aeon authoring importer.

No upstream model or solver executes at Aeon runtime. Install MiniZinc 2.9.4
separately and supply a checkout of the upstream commit in catalogue.json.
Instance parameters are explicit, versioned data rather than inferred defaults.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
import sys
from pathlib import Path
import subprocess


def prepare(upstream, minizinc, cache, catalogue, instances, timeout, capture_python=None):
    metadata = json.loads(catalogue.read_text())
    records = {entry["id"]: entry for entry in metadata["models"]}
    configured = json.loads(instances.read_text())
    hashes = {source["path"]: source["sha256"] for entry in records.values() for source in entry["sources"]}
    cache.mkdir(parents=True, exist_ok=True)
    solver = cache / "aeon-generic.msc"
    solver.write_text(
        json.dumps(
            dict(
                id="org.aeon.generic",
                name="Aeon compiler",
                version="1",
                executable="/bin/false",
                mznlib="",
                supportsMzn=False,
                supportsFzn=True,
                needsSolns2Out=False,
            )
        )
    )
    version = subprocess.run([str(minizinc), "--version"], capture_output=True, text=True, check=True)
    if "2.9.4" not in version.stdout:
        raise ValueError("Reproducible preparation requires MiniZinc 2.9.4")

    def compile_one(item):
        anchor, instance = item
        result = dict(anchor=anchor, name=records[anchor]["name"], **instance)
        paths = list(instance["input_sha256"])
        for path in paths:
            digest = hashlib.sha256((upstream / path).read_bytes()).hexdigest()
            if digest != instance["input_sha256"][path] or (path in hashes and digest != hashes[path]):
                raise ValueError(f"Source checksum mismatch: {path}")
        result["input_sha256"] = {path: hashlib.sha256((upstream / path).read_bytes()).hexdigest() for path in paths}
        prepared_source = upstream / instance["source"]
        if instance.get("authoring") == "cpmpy":
            prepared_source = cache / (anchor + ".reference.mzn")
            capture_command = [
                str(capture_python or sys.executable),
                str(Path(__file__).with_name("capture_hakank_cpmpy.py")),
                "--source",
                str(upstream / instance["source"]),
                "--destination",
                str(prepared_source),
                "--minizinc",
                str(minizinc),
            ]
            for data_script in instance["data_files"]:
                capture_command += ["--data-script", str(upstream / data_script)]
            try:
                captured = subprocess.run(
                    capture_command,
                    cwd=upstream / "cpmpy",
                    env={**os.environ, "PYTHONHASHSEED": "0"},
                    capture_output=True,
                    text=True,
                    timeout=timeout,
                )
            except subprocess.TimeoutExpired:
                return {**result, "compiled": False, "error": "reference capture timeout"}
            if captured.returncode:
                return {**result, "compiled": False, "error": captured.stderr[-4000:]}
            actual = json.loads(captured.stdout.splitlines()[-1])
            if actual["captured_sha256"] != instance["capture"]["captured_sha256"] or (
                instance["capture"].get("numpy_version")
                and actual["numpy_version"] != instance["capture"]["numpy_version"]
            ):
                return {**result, "compiled": False, "error": "reference capture checksum mismatch"}
        command = [
            str(minizinc),
            "--compile",
            "--solver",
            str(solver),
            str(prepared_source),
            "--output-fzn-to-file",
            str(cache / (anchor + ".fzn")),
            "--output-ozn-to-file",
            str(cache / (anchor + ".ozn")),
        ]
        if instance.get("authoring") != "cpmpy":
            command += [str(upstream / path) for path in instance["data_files"]]
            command += [f"-D{name}={value}" for name, value in instance["parameters"].items()]
        try:
            process = subprocess.run(command, capture_output=True, text=True, timeout=timeout)
            result["compiled"] = process.returncode == 0
            if process.returncode:
                result["error"] = process.stderr.replace(str(upstream), "<upstream>").replace(str(cache), "<cache>")[
                    -4000:
                ]
        except subprocess.TimeoutExpired:
            result.update(compiled=False, error="compilation timeout")
        return result

    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(compile_one, configured.items()))
    (cache / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    return sum(bool(item["compiled"]) for item in results), len(results)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", required=True, type=Path)
    parser.add_argument("--minizinc", required=True, type=Path)
    parser.add_argument("--cache", required=True, type=Path)
    parser.add_argument("--catalogue", type=Path, default=Path("examples/synthesis/hakank/catalogue.json"))
    parser.add_argument("--instances", type=Path, default=Path("examples/synthesis/hakank/prepared_instances.json"))
    parser.add_argument("--timeout", type=float, default=30)
    parser.add_argument(
        "--capture-python", type=Path, help="Interpreter with pinned optional CPMpy authoring dependencies"
    )
    args = parser.parse_args()
    print(
        prepare(
            args.upstream.resolve(),
            args.minizinc.resolve(),
            args.cache.resolve(),
            args.catalogue,
            args.instances,
            args.timeout,
            args.capture_python,
        )
    )


if __name__ == "__main__":
    main()
