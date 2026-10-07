"""Tests for the DACE data-completion examples (FTA paper, OOPSLA'17).

Covers (a) the Table DSL worked pipelines -- including the reshape operators
whose binding module path this work fixed -- and (b) a per-cell completion run
by the FTA backend.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from collections import Counter

import pytest

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _manifest() -> dict:
    manifest_path = os.path.join(REPO, "examples/synthesis/dace/reconstructed_manifest.json")
    with open(manifest_path, encoding="utf-8") as manifest_file:
        return json.load(manifest_file)


def test_reconstructed_catalog_has_84_entries():
    manifest = _manifest()
    assert manifest["total_tasks"] == 84
    assert len(manifest["published_tasks"]) == 6
    assert len(manifest["reconstructed_tasks"]) == 78
    assert sum(manifest["paper_category_totals"].values()) == 84
    for task in manifest["published_tasks"] + manifest["reconstructed_tasks"]:
        assert os.path.isfile(os.path.join(REPO, task["file"]))


def test_catalog_group_totals_match_paper():
    # Section 6 of the paper: 46 imputation, 32 spreadsheet, 6 relational tasks.
    manifest = _manifest()
    required = {"imputation": 46, "spreadsheet": 32, "relational": 6}
    assert manifest["group_totals"] == required
    counted = Counter(task["group"] for task in manifest["published_tasks"] + manifest["reconstructed_tasks"])
    assert dict(counted) == required


def test_published_tasks_occupy_identified_category_slots():
    # The six published examples are excluded from the 78 reconstructed files;
    # each occupies one identified slot in its paper category.
    manifest = _manifest()
    published = manifest["published_tasks"]
    assert sorted(task["category"] for task in published) == [1, 3, 4, 5, 9, 13]
    assert all(task["status"] == "published" for task in published)
    assert not {task["file"] for task in published} & {task["file"] for task in manifest["reconstructed_tasks"]}
    per_category = Counter(task["category"] for task in published + manifest["reconstructed_tasks"])
    assert {str(category): count for category, count in per_category.items()} == manifest["paper_category_totals"]


def test_category_21_is_not_counted_as_a_successful_reconstruction():
    manifest = _manifest()
    not_expressible = [task for task in manifest["reconstructed_tasks"] if task["status"] == "not-expressible"]
    assert [task["id"] for task in not_expressible] == ["21.1"]
    assert all(task["category"] == 21 for task in not_expressible)
    summary = manifest["summary"]
    assert summary["published"] == 6
    assert summary["reconstructed_expressible"] == 77
    assert summary["reconstructed_not_expressible"] == 1
    assert summary["expressible_total"] == 83
    assert summary["not_expressible_tasks"] == ["21.1"]
    assert (
        summary["total_tasks"]
        == summary["published"] + summary["reconstructed_expressible"] + summary["reconstructed_not_expressible"]
    )


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
        ("complete_product", "24 + 32"),  # FTA may return an observationally equal sum
        ("complete_diff", "5"),
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
        ("delta", "col_at"),  # Fig. 1: difference of two cells (MINUS)
        ("col_at_plus", "col_at"),  # smoke: col_at + 1
    ],
)
def test_fta_pbe_completion(example: str, token: str):
    out = _run(["--no-main", "-s", "fta", "--budget", "60", f"examples/synthesis/dace/pbe/{example}.ae"])
    assert "no spec-consistent program" not in out, out[-1500:]
    assert "?hole:" in out, out[-1500:]
    assert token in out, out[-1500:]
