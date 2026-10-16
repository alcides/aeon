import json
import sys
from dataclasses import dataclass
from pathlib import Path

import pytest

from aeon.benchmarks.monotonicity import TASKS, MonotonicityBenchmark, main
from aeon.benchmarks.monotonicity_runner import run
from aeon.synthesis.api import UnsupportedSynthesisGoal


@pytest.mark.parametrize("task", TASKS)
def test_program_backend_rejected_as_unsupported(task):
    with pytest.raises(UnsupportedSynthesisGoal):
        MonotonicityBenchmark(task).synthesize("ortools", 1)


def test_proof_cli_reports_capability_mismatch(monkeypatch, capsys):
    monkeypatch.setattr(sys, "argv", ["proof", "--task", "identity", "--backend", "ortools"])
    assert main() == 2
    assert json.loads(capsys.readouterr().out)["status"] == "unsupported_goal"


def test_evaluation_adapter_records_unsupported_instead_of_crashing():
    events = []

    class Unsupported:
        def __init__(self, *args):
            pass

        def synthesize(self, **kwargs):
            raise UnsupportedSynthesisGoal("per-hole backend required")

    assert run(Path("identity.ae"), "ortools", 1, lambda event, **data: events.append((event, data)), Unsupported) == 2
    assert events[-1] == ("results", {"holes": {}})
    assert any(event == "unsupported_goal" for event, data in events)


def test_evaluation_adapter_retains_independent_proof_gate():
    @dataclass
    class Proof:
        candidate: str = "x"
        accepted: bool = False

    class Benchmark:
        def __init__(self, *args):
            pass

        def synthesize(self, **kwargs):
            return Proof()

        def verify(self, candidate):
            return Proof()

    events = []
    assert (
        run(Path("identity.ae"), "random_search", 1, lambda event, **data: events.append((event, data)), Benchmark) == 2
    )
    assert events[-1] == ("results", {"holes": {}})
    assert events[-2][1]["objective_verified"] is False
