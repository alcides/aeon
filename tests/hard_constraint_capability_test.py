"""Hard constraints must remain hard when the selected backend lacks support."""

import subprocess
import sys

import pytest

from aeon.backend.evaluator import EvaluationContext
from aeon.core.terms import Literal
from aeon.core.types import t_int
from aeon.synthesis.api import UnsupportedSynthesisGoal
from aeon.synthesis.decorators import Goal
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.modules.random_search import RandomSearchSynthesizer
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def test_hard_constraints_reject_incompatible_backend_before_search():
    name = Name("constraint", 0)
    with pytest.raises(UnsupportedSynthesisGoal, match="@require"):
        synthesize_holes(
            TypingContext(),
            EvaluationContext(),
            Literal(0, t_int),
            [],
            {name: {"goals": [Goal(True, 1, name, "constraint")]}},
            RandomSearchSynthesizer(),
        )


@pytest.mark.parametrize("backend", ["gp", "smt"])
def test_hakank_cli_reports_controlled_unsupported_goal(backend):
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "aeon",
            "--no-main",
            "-s",
            backend,
            "--budget",
            "1",
            "examples/synthesis/hakank/all_different_except_0.ae",
        ],
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert result.returncode == 2
    assert "Unsupported synthesis goal: @require" in result.stderr
    assert "Traceback" not in result.stderr
