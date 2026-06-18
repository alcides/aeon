"""Tests for the DACE data-completion examples (FTA paper, OOPSLA'17).

Covers (a) the Table DSL worked pipelines -- including the reshape operators
whose binding module path this work fixed -- and (b) a per-cell completion run
by the FTA backend.
"""

from __future__ import annotations

import os
import subprocess
import sys

import pytest

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _run(args: list[str]) -> str:
    proc = subprocess.run(
        [sys.executable, "-m", "aeon", *args],
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=120,
    )
    out = proc.stdout + proc.stderr
    assert "Traceback" not in proc.stderr, out[-2000:]
    return out


@pytest.mark.parametrize(
    "example,expected",
    [
        ("column_formula", "33"),  # mutate + sum_col
        ("aggregate_sum", "35"),  # sum_col
        ("group_average", "15"),  # filter + mean_col
        ("running_balance", "12"),  # cumsum + cell
        ("pivot_wide", "7"),  # pivot + cell (binding-path fix)
        ("melt_long", "8"),  # melt + cell (binding-path fix)
        ("filter_aggregate", "15"),  # filter + sum_col
        ("join_lookup", "41"),  # join + mutate + sum_col
    ],
)
def test_table_pipeline_runs(example: str, expected: str):
    out = _run([f"examples/synthesis/dace/{example}.ae"])
    assert expected in out.split(), out[-1500:]


@pytest.mark.parametrize(
    "example,value",
    [
        ("complete_total", "15"),
        ("complete_average", "10"),
        ("complete_max", "8"),
    ],
)
def test_fta_completes_cell(example: str, value: str):
    out = _run(["--no-main", "-s", "fta", "--budget", "10", f"examples/synthesis/dace/synth/{example}.ae"])
    assert f"?hole: {value}" in out, out[-1500:]


# Programming-by-example completions: the paper's actual mechanism. Each hole is
# a *function of the missing-cell index* specified by @example input/output rows;
# the FTA keys states by the output vector over those examples and composes the
# table primitives (and a conditional) to reproduce them. ``token`` is a
# primitive the intended completion must use, evidence it reads the table.
@pytest.mark.parametrize(
    "example,token",
    [
        ("locf", "prev_nonmissing"),  # 2.1: previous non-missing + 1
        ("prev_sameid", "prev_sameid"),  # 2.2: previous with same id (relational)
        ("turns", "down_first_nonzero"),  # 2.3: up to value 1, then down to non-zero
        ("group_count", "group_count"),  # 2.4: COUNT of the group
        ("fallback", "if"),  # 2.5: previous else next (conditional)
    ],
)
def test_fta_pbe_completion(example: str, token: str):
    out = _run(["--no-main", "-s", "fta", "--budget", "60", f"examples/synthesis/dace/pbe/{example}.ae"])
    assert "no spec-consistent program" not in out, out[-1500:]
    assert "?hole:" in out, out[-1500:]
    assert token in out, out[-1500:]
