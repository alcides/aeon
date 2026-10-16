"""Protect proof-task routing and prevent unproved candidates being successes."""

from dataclasses import dataclass
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("monotonicity_worker", ROOT / "scripts/monotonicity_worker.py")
worker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(worker)


@dataclass
class Result:
    candidate: str
    status: str

    @property
    def accepted(self):
        return self.status == "proved"


class RoutingTests(unittest.TestCase):
    def test_only_declared_proof_tasks_are_routed(self):
        source = Path("/some/checkout")
        for task in worker.TASKS:
            self.assertTrue(worker.is_monotonicity_case(source, source / f"examples/synthesis/monotonicity/{task}.ae"))
        self.assertFalse(worker.is_monotonicity_case(source, source / "examples/other/identity.ae"))
        self.assertFalse(worker.is_monotonicity_case(source, source / "examples/synthesis/monotonicity/unknown.ae"))

    def test_final_proof_gate_rejects_backend_output(self):
        for verified, exit_code, expected in [(True, 0, {"?body": "x"}), (False, 2, {})]:
            with self.subTest(verified=verified):
                calls = []
                events = []

                class Benchmark:
                    def __init__(self, task, directory):
                        pass

                    def synthesize(self, backend, budget):
                        calls.append((backend, budget))
                        return Result("x", "proved")

                    def verify(self, candidate):
                        return Result(candidate, "proved" if verified else "disproved")

                result = worker.run(
                    Path("/tasks/identity.ae"),
                    "random_search",
                    5,
                    lambda event, **data: events.append((event, data)),
                    Benchmark,
                )
                self.assertEqual(result, exit_code)
                self.assertEqual(calls, [("random_search", 5)])
                self.assertEqual(events[-1][1]["holes"], expected)
                self.assertEqual(events[-2][1]["objective_verified"], verified)

    def test_no_solution_is_not_a_crash_or_filled_hole(self):
        class Benchmark:
            def __init__(self, *args):
                pass

            def synthesize(self, **kwargs):
                return None

        events = []
        self.assertEqual(
            worker.run(
                Path("/tasks/relu.ae"),
                "random_search",
                5,
                lambda event, **data: events.append((event, data)),
                Benchmark,
            ),
            2,
        )
        self.assertEqual(events[-1][1]["holes"], {})


if __name__ == "__main__":
    unittest.main()
