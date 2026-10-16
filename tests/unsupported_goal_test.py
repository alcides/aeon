import subprocess
import sys

import pytest

from aeon.benchmarks.outcomes import unsupported_goal
from aeon.synthesis.api import UnsupportedSynthesisGoal, SynthesisNotSuccessful


@pytest.mark.parametrize(
    "diagnostic",
    [
        "CPSatHole cannot translate the objective (Application). Use a grammar-based synthesizer",
        "CPSatHole cannot translate the objective (If).",
        "CPSatHole cannot translate the objective (operator 'shipping_cost').",
        "CPSatHole cannot handle hole h (type String).",
        "CPSatHole requires at least one @minimize/@maximize objective.",
        str(UnsupportedSynthesisGoal("unsupported input")),
    ],
)
def test_unsupported_classification_covers_old_and_new_diagnostics(diagnostic):
    assert unsupported_goal(diagnostic)


def test_other_solver_failures_are_not_mislabeled():
    assert not unsupported_goal("AssertionError: objective translator invariant failed")
    assert not unsupported_goal("Z3Exception: Sort mismatch")
    assert isinstance(UnsupportedSynthesisGoal("no objective"), SynthesisNotSuccessful)


def test_ortools_unsupported_cli_returns_two_without_traceback(tmp_path):
    pytest.importorskip("ortools")
    path = tmp_path / "no_objective.ae"
    path.write_text("def x:Int := ?hole;")
    result = subprocess.run(
        [sys.executable, "-m", "aeon", "--no-main", "-s", "ortools", str(path)],
        capture_output=True,
        text=True,
        timeout=15,
    )
    assert result.returncode == 2
    assert unsupported_goal(result.stderr)
    assert "Traceback" not in result.stderr
