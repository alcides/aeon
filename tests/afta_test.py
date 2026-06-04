"""Tests for the AFTA (Abstraction-Refinement Finite Tree Automata) backend.

AFTA (Wang, Dillig & Singh, POPL'18) is the abstract-state successor of the
concrete ``fta`` backend: it keys automaton states by a candidate's image under
a *predicate abstraction* (a truth-vector over predicates drawn from the hole's
refinement) rather than its concrete output, so many outputs collapse to one
state. It starts from the coarsest abstraction and runs a CEGAR loop --
extract the smallest abstractly-accepting program, ``validate`` it, and on a
spurious acceptance refine the predicate set with a violated goal conjunct --
until a validated program is found. Like ``fta`` it needs no objective.
"""

from __future__ import annotations

import os
import subprocess
import sys

from aeon.core.terms import Literal
from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.modules.afta import AFTASynthesizer
from aeon.synthesis.modules.afta.synthesizer import _conjuncts, _eval_pred, _Unevaluable
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.utils.name import Name
from tests.driver import check_and_return_core

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _solve(code: str, budget: float = 15.0):
    term, ctx, ectx, metadata = check_and_return_core(code)
    targets = incomplete_functions_and_holes(ctx, term)
    holes = synthesize_holes(ctx, ectx, term, targets, metadata, AFTASynthesizer(), budget=budget)
    return holes[next(iter(holes))]


def test_factory_registers_afta():
    assert isinstance(make_synthesizer("afta"), AFTASynthesizer)


def test_solves_linear_refinement():
    # The coarse abstraction first accepts a wrong value; CEGAR adds the
    # violated conjunct v + 4 == 7, splitting the state down to the answer.
    t = _solve("def n : {v:Int | v + 4 == 7} = ?hole;")
    assert isinstance(t, Literal) and t.value == 3


def test_solves_conjoined_refinement_via_refinement():
    # Two conjuncts: AFTA refines the abstraction until both predicates pin the
    # single satisfying value, validated once at the accepting abstract state.
    t = _solve("def m : {v:Int | v * 2 == 10 && v - 1 == 4} = ?hole;")
    assert isinstance(t, Literal) and t.value == 5


def test_solves_three_conjunct_refinement():
    # Three conjuncts drive multiple CEGAR rounds (v > 0, v % 5 == 0, v + 7 ==
    # 17) -> 10. Exercises modulo in the predicate evaluator.
    t = _solve("def k : {v:Int | v > 0 && v % 5 == 0 && v + 7 == 17} = ?hole;")
    assert isinstance(t, Literal) and t.value == 10


def test_conjuncts_flattens_top_level_and():
    # v == 1 && v == 2 && v == 3  parses right-associated; the splitter flattens
    # it to three atomic predicates.
    term, ctx, ectx, metadata = check_and_return_core("def n : {v:Int | v == 1 && v == 2 && v == 3} = ?hole;")
    targets = incomplete_functions_and_holes(ctx, term)
    from aeon.core.types import top
    from aeon.synthesis.identification import get_holes_info

    info = get_holes_info(ctx, term, top, targets, refined_types=True)
    ty = next(t for t, _c in info.values() if hasattr(t, "refinement"))
    assert len(_conjuncts(ty.refinement)) == 3


def test_eval_pred_supported_and_unsupported():
    v = Name("v", 0)
    # v + 4 == 7  with v := 3  is True; with v := 4 is False.
    atom = LiquidApp(
        Name("==", 0),
        [LiquidApp(Name("+", 0), [LiquidVar(v), LiquidLiteralInt(4)]), LiquidLiteralInt(7)],
    )
    assert _eval_pred(atom, v, 3) is True
    assert _eval_pred(atom, v, 4) is False
    # Arithmetic on a non-numeric output is treated as unevaluable (excluded
    # from the abstraction), never an error -- validate remains the oracle.
    try:
        _eval_pred(atom, v, "not-a-number")
        assert False, "expected _Unevaluable"
    except _Unevaluable:
        pass


def test_cli_runs_afta_backend():
    # End-to-end through the real driver: the hole is filled with the value that
    # satisfies the three-conjunct refinement, with no objective decorator.
    proc = subprocess.run(
        [
            sys.executable,
            "-m",
            "aeon",
            "--no-main",
            "-s",
            "afta",
            "--budget",
            "10",
            "examples/synthesis/afta/abstraction_refinement.ae",
        ],
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=120,
    )
    out = proc.stdout + proc.stderr
    assert "Traceback" not in proc.stderr, out[-2000:]
    assert "?hole: 10" in out, out[-2000:]
