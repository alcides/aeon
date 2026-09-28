"""Tests for Pareto-front display helpers in the synthesis UI."""

from __future__ import annotations

import random
from io import StringIO
from unittest.mock import patch

from aeon.core.terms import Literal
from aeon.core.types import t_int
from aeon.synthesis.uis.api import PARETO_DISPLAY_LIMIT
from aeon.synthesis.uis.terminal import (
    TerminalUI,
    format_pareto_front_lines,
    select_pareto_display,
)
from aeon.typechecking.context import TypingContext
from aeon.backend.evaluator import EvaluationContext


def test_select_pareto_display_keeps_small_front():
    front = [([float(i)], Literal(i, t_int)) for i in range(3)]
    assert select_pareto_display(front) == front


def test_select_pareto_display_samples_when_larger_than_limit():
    front = [([float(i)], Literal(i, t_int)) for i in range(PARETO_DISPLAY_LIMIT + 5)]
    rng = random.Random(0)
    shown = select_pareto_display(front, limit=PARETO_DISPLAY_LIMIT, rng=rng)
    assert len(shown) == PARETO_DISPLAY_LIMIT
    assert all(item in front for item in shown)


def test_format_pareto_front_lines_lists_members():
    front = [
        ([0.2, 0.0], Literal(0, t_int)),
        ([0.1, 32.0], Literal(1, t_int)),
    ]
    lines = format_pareto_front_lines(front, elapsed_time=3.5, budget=10)
    assert lines[0] == "# pareto t=3.5s/10s size=2"
    assert "0.2" in lines[1] and "0.0" in lines[1]
    assert "0.1" in lines[2] and "32.0" in lines[2]


def test_format_pareto_front_lines_notes_sampling():
    front = [([float(i)], Literal(i, t_int)) for i in range(15)]
    lines = format_pareto_front_lines(front, elapsed_time=1.0, budget=5, limit=10, rng=random.Random(1))
    assert "showing 10 of 15" in lines[0]
    assert len(lines) == 11  # header + 10 members


def test_terminal_ui_register_front_prints_archive():
    ui = TerminalUI()
    with patch("sys.stdout", new_callable=StringIO) as out:
        ui.start(TypingContext(), EvaluationContext(), "hole", t_int, 10)
        ui.register_front([([0.5, 16.0], Literal(3, t_int))], 2.0)
        text = out.getvalue()
    assert "# pareto t=2.0s/10s size=1" in text
    assert "0.5" in text
