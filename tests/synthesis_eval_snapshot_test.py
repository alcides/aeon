"""Evaluation snapshots support editable checkouts without an optional uv lock."""

import importlib.util
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace


def test_snapshot_without_uv_lock(tmp_path, monkeypatch):
    script = Path(__file__).resolve().parents[1] / "benchmarks/synthesis_eval/scripts/eval.py"
    spec = importlib.util.spec_from_file_location("snapshot_evaluation", script)
    runner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(runner)
    source = tmp_path / "checkout"
    source.mkdir()
    subprocess.run(["git", "init", "-q", str(source)], check=True)
    (source / "example.ae").write_text("def n:Int := 0;")
    subprocess.run(["git", "add", "example.ae"], cwd=source, check=True)
    subprocess.run(
        ["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid", "commit", "-qm", "fixture"],
        cwd=source,
        check=True,
    )
    root = tmp_path / "experiment"
    monkeypatch.setattr(runner, "ROOT", root)
    runner.snapshot(SimpleNamespace(source=str(source)))
    assert (root / "source/aeon/example.ae").is_file()
    assert not (root / "source/aeon/uv.lock").exists()
    provenance = json.loads((root / "source/provenance.json").read_text())
    assert provenance["snapshot_sha256"]
    assert provenance["commit"] == subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=source, text=True).strip()
