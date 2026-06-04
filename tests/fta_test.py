"""Tests for the FTA (Finite Tree Automata) synthesis backend.

FTA builds a finite tree automaton bottom-up, keying states by a candidate's
concrete output (observational equivalence) and accepting the states consistent
with the refinement-typed spec (so the spec is checked once per state). Unlike
the metric backend (``symetric``), it needs no objective: a pure refinement hole
is enough, and it extracts the smallest accepted program.
"""

from __future__ import annotations

import os
import subprocess
import sys

from aeon.core.terms import Literal
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.modules.fta import FTASynthesizer
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from tests.driver import check_and_return_core

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _solve(code: str, budget: float = 15.0):
    term, ctx, ectx, metadata = check_and_return_core(code)
    targets = incomplete_functions_and_holes(ctx, term)
    holes = synthesize_holes(ctx, ectx, term, targets, metadata, FTASynthesizer(), budget=budget)
    return holes[next(iter(holes))]


def test_factory_registers_fta():
    assert isinstance(make_synthesizer("fta"), FTASynthesizer)


def test_solves_linear_refinement():
    # The accepting state is the integer satisfying v + 4 == 7.
    t = _solve("def n : {v:Int | v + 4 == 7} = ?hole;")
    assert isinstance(t, Literal) and t.value == 3


def test_solves_conjoined_refinement():
    # Two constraints pin a single value; FTA validates one rep per output value.
    t = _solve("def m : {v:Int | v * 2 == 10 && v - 1 == 4} = ?hole;")
    assert isinstance(t, Literal) and t.value == 5


def test_cli_runs_fta_backend():
    # End-to-end through the real driver: the hole is filled with the value that
    # satisfies the refinement, with no objective decorator required.
    proc = subprocess.run(
        [
            sys.executable,
            "-m",
            "aeon",
            "--no-main",
            "-s",
            "fta",
            "--budget",
            "10",
            "examples/synthesis/fta/arithmetic_refinement.ae",
        ],
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=120,
    )
    out = proc.stdout + proc.stderr
    assert "Traceback" not in proc.stderr, out[-2000:]
    assert "?hole: 3" in out, out[-2000:]
