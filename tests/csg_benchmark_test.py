"""Validation for the inverse-CSG benchmark suite (examples/synthesis/csg/).

Reproduces the benchmark of Feser, Dillig & Solar-Lezama, "Metric Program
Synthesis for Inverse CSG" (arXiv:2206.06164). These tests check that:

  * every committed target PNG is exactly the bitmap of its original program
    (i.e. the reference solution reconstructs the target, distance 0), and
  * every generated `.ae` benchmark parses and type-checks in Aeon.

A single end-to-end test runs one benchmark through Aeon synthesis to exercise
the native (PIL) metric over the FFI boundary. The full synthesis sweep is left
out of run_examples.sh because each instance is a hard, full-budget search.
"""

from __future__ import annotations

import os
import subprocess
import sys

import pytest

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CSG = os.path.join(REPO, "examples", "synthesis", "csg")
sys.path.insert(0, CSG)

import csg_metric  # noqa: E402
from generate import parse, to_runtime  # noqa: E402


def _benchmarks():
    rows = []
    with open(os.path.join(CSG, "benchmarks.tsv")) as fh:
        for line in fh:
            line = line.rstrip("\n")
            if line:
                cat, name, sexpr = line.split("\t")
                rows.append((cat, name, sexpr.strip()))
    return rows


BENCHMARKS = _benchmarks()


def test_suite_is_complete():
    # The paper evaluates 40 benchmarks (tiny + small + generated); the full
    # cad_ext suite (including medium/large) has 47.
    assert len(BENCHMARKS) == 47
    cats = {c for c, _, _ in BENCHMARKS}
    assert cats == {"tiny", "small", "medium", "large", "generated"}


@pytest.mark.parametrize("cat,name,sexpr", BENCHMARKS, ids=[f"{c}/{n}" for c, n, _ in BENCHMARKS])
def test_reference_reconstructs_target(cat, name, sexpr):
    """The original program renders to exactly the committed target bitmap."""
    ref = to_runtime(parse(sexpr))
    png = os.path.join(CSG, "targets", f"csg_{cat}_{name}.png")
    assert os.path.exists(png), f"missing target image: {png}"
    assert csg_metric.score(ref, png) == 0


@pytest.mark.parametrize("cat,name,sexpr", BENCHMARKS, ids=[f"{c}/{n}" for c, n, _ in BENCHMARKS])
def test_benchmark_parses_and_typechecks(cat, name, sexpr):
    """The generated .ae benchmark parses and type-checks (no synthesis)."""
    from aeon.facade.driver import AeonConfig, AeonDriver
    from aeon.synthesis.uis.api import SynthesisFormat, SynthesisUI

    cfg = AeonConfig(
        synthesizer="random_search",
        synthesis_ui=SynthesisUI(),
        synthesis_budget=1,
        timings=False,
        no_main=True,
        synthesis_format=SynthesisFormat.DEFAULT,
    )
    errors = AeonDriver(cfg).parse(os.path.join(CSG, f"csg_{cat}_{name}.ae"))
    assert errors == []


def test_native_metric_end_to_end():
    """Run one benchmark through Aeon synthesis to exercise the FFI metric."""
    proc = subprocess.run(
        [sys.executable, "-m", "aeon", "--no-main", "--budget", "1", "examples/synthesis/csg/csg_tiny_two_circle.ae"],
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=120,
    )
    # 0 = solved, 2 = no program found within budget; both are valid outcomes.
    assert proc.returncode in (0, 2), proc.stderr[-2000:]
    assert "Type error" not in proc.stdout and "Type error" not in proc.stderr
