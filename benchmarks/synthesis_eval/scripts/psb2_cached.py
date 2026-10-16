"""Provide fresh copies of prepared, real PSB2 samples without network access."""

import hashlib
import json
from pathlib import Path


def install(directory):
    import psb2

    directory = Path(directory)
    manifest = json.loads((directory / "manifest.json").read_text())
    records = {row["problem"]: row for row in manifest}

    def fetch_examples(datasets_directory, problem_name, n_train, n_test, format="psb2", seed=None):
        record = records[problem_name]
        if (
            format != "lists"
            or n_train != record["train_count"]
            or n_test != record["test_count"]
            or seed not in (None, 0)
        ):
            raise ValueError("Prepared PSB2 sample request does not match cached counts, lists format or seed 0")
        file = directory / f"{problem_name}.json"
        raw = file.read_bytes()
        if hashlib.sha256(raw).hexdigest() != records[problem_name]["samples_sha256"]:
            raise ValueError(f"PSB2 sample checksum changed: {problem_name}")
        data = json.loads(raw)
        if len(data["train"]) != n_train or len(data["test"]) != n_test:
            raise ValueError(f"PSB2 sample count mismatch: {problem_name}")
        return data["train"], data["test"]

    psb2.fetch_examples = fetch_examples
