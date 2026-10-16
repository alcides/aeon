"""Storage failures retain evidence and never become no-solution outcomes."""

import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("storage_evaluation", ROOT / "scripts/eval.py")
evaluation = importlib.util.module_from_spec(spec)
spec.loader.exec_module(evaluation)


class StorageHarnessTests(unittest.TestCase):
    def fixture(self, folder):
        run = Path(folder)
        source = run / "source"
        source.mkdir()
        (source / "case.ae").write_text("def x:Int := ?hole;")
        (run / "results").mkdir()
        evaluation.write_json(run / "plan.json", {"source": str(source), "source_sha256": "fixture"})
        job = {"id": 0, "case": "case.ae", "algorithm": "smt", "seed": 0, "budget_s": 1, "timeout_s": 5}
        return run, job

    def test_excessive_output_is_infrastructure_error(self):
        with tempfile.TemporaryDirectory() as folder:
            run, job = self.fixture(folder)
            fake = run / "fake-python"
            fake.write_text("#!" + sys.executable + '\nimport sys\nsys.stdout.buffer.write(b"x" * 20000000)\n')
            fake.chmod(0o755)
            evaluation.execute(run, job, str(fake))
            result = json.loads((run / "results/0000000.json").read_text())
            self.assertEqual(result["status"], "infrastructure_error")
            self.assertIn("output limit", result["infrastructure_detail"])
            self.assertTrue((run / "results/0000000.stdout").exists())
            self.assertFalse((run / "results/0000000.lock").exists())

    def test_failed_preflight_leaves_no_stale_lock(self):
        with tempfile.TemporaryDirectory() as folder:
            run, job = self.fixture(folder)
            tools = evaluation.storage_tools()
            usage = type("Usage", (), {"free": 0})()
            with patch.object(tools.shutil, "disk_usage", return_value=usage):
                with self.assertRaises(tools.StorageLimitError):
                    evaluation.execute(run, job, "/unused/python")
            self.assertFalse((run / "results/0000000.lock").exists())
