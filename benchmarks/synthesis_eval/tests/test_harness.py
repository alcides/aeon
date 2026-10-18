import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("evaluation", Path(__file__).resolve().parents[1] / "scripts/eval.py")
evaluation = importlib.util.module_from_spec(spec)
spec.loader.exec_module(evaluation)


class HarnessTests(unittest.TestCase):
    def test_json_output_has_trailing_program(self):
        text = 'progress\nSynthesized holes:\n{"?x": "(if true then 1 else 2)", "?y": "5"}\nSynthesized:\nprogram'
        self.assertEqual(evaluation.parse_holes(text), {"?x": "(if true then 1 else 2)", "?y": "5"})

    def test_malformed_or_absent_results(self):
        for text in ("", "No holes to synthesize.", "Synthesized holes:\n{", "Synthesized holes:\n[]"):
            self.assertEqual(evaluation.parse_holes(text), {})

    def test_features_ignore_comment_and_string_holes(self):
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder)
            p = source / "problem.ae"
            p.write_text(
                '# ?comment\n// ?other\ndef s : String := "?string";\n@minimize_int(0)\ndef f : {v:Int | v > 10 || v < 0} := ?x;\ndef g : Int := ?x;'
            )
            f = evaluation.features(p, source)
            self.assertEqual(f["hole_names"], ["x"])
            self.assertEqual(f["refinements"], 1)
            self.assertTrue(f["uses_disjunction"])
            self.assertTrue(f["fitness"])

    def test_process_outcomes_and_hard_deadline(self):
        cases = [
            ('printf \'Synthesized holes:\\n{"?x":"1","?y":"2"}\\n\'; exit 0', "filled", 2),
            ('printf \'Synthesized holes:\\n{"?x":"1"}\\n\'; exit 0', "incomplete", 2),
            ('printf \'Synthesized holes:\\n{"?x":"1","?y":"2"}\\n\'; exit 1', "error", 2),
            ("sleep 10", "timeout", 0.1),
        ]
        for body, expected, timeout in cases:
            with self.subTest(status=expected), tempfile.TemporaryDirectory() as folder:
                run = Path(folder)
                source = run / "source"
                source.mkdir()
                (source / "case.ae").write_text("def a : Int := ?x; def b : Int := ?y;")
                (run / "results").mkdir()
                evaluation.write_json(run / "plan.json", {"source": str(source), "source_sha256": "fixture"})
                fake_python = run / "fake-python"
                fake_python.write_text("#!/bin/sh\n" + body + "\n")
                fake_python.chmod(0o755)
                job = {"id": 0, "case": "case.ae", "algorithm": "smt", "seed": 0, "budget_s": 1, "timeout_s": timeout}
                evaluation.execute(run, job, str(fake_python))
                result = evaluation.read_json(run / "results/0000000.json")
                self.assertEqual(result["status"], expected)
                self.assertFalse((run / "results/0000000.lock").exists())
                if expected == "timeout":
                    self.assertLess(result["elapsed_s"], 2)

    def test_atomic_result_write(self):
        with tempfile.TemporaryDirectory() as folder:
            p = Path(folder) / "nested/result.json"
            evaluation.write_json(p, {"status": "timeout"})
            self.assertEqual(evaluation.read_json(p), {"status": "timeout"})
            self.assertFalse(p.with_suffix(".json.tmp").exists())


if __name__ == "__main__":
    unittest.main()
