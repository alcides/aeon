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
    t = _solve("def n : {v:Int | v + 4 = 7} := ?hole;")
    assert isinstance(t, Literal) and t.value == 3


def test_solves_conjoined_refinement():
    # Two constraints pin a single value; FTA validates one rep per output value.
    t = _solve("def m : {v:Int | v * 2 = 10 && v - 1 = 4} := ?hole;")
    assert isinstance(t, Literal) and t.value == 5


# Example-driven mode (paper-faithful PBE): @example / @csv give concrete
# input/output rows; FTA keys states by the candidate's output vector over those
# inputs and accepts the one matching the expected outputs. With distinct
# expected outputs, no constant can satisfy them, so any solution must read the
# input -- i.e. FTA synthesizes a function *of its input*.


def test_solves_input_dependent_from_examples():
    t = _solve(
        "@example(succ 1 = 2)\n@example(succ 4 = 5)\n@example(succ 9 = 10)\ndef succ (x:Int) : Int := ?hole;",
        budget=25.0,
    )
    assert t is not None and not isinstance(t, Literal)  # reads x (it's x + 1)


def test_solves_input_dependent_from_csv():
    t = _solve(
        '@csv_data("1.0,2.0\\n3.0,6.0\\n4.0,8.0")\ndef double (x:Float) : Float := ?hole;',
        budget=25.0,
    )
    assert t is not None and not isinstance(t, Literal)  # reads x (it's x + x)


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
