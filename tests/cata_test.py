"""Tests for the CATA (Constraint-Annotated Tree Automata) backend.

CATA is the recursive/relational tree-automata backend, after ``fta`` (concrete)
and ``afta`` (abstract). It targets relational refinements (relating a
function's parameters to its result), discharging each candidate with the liquid
typechecker -- which performs exactly CATA's constraint-annotation check,
including the inductive hypothesis for recursive calls and a termination proof.

Over FTA/AFTA's construction it adds: monomorphic components from polymorphic
Num/Ord operators, conditional (case-split) transitions, and recursive
self-calls as ordinary components. These tests cover the machinery that reliably
converges -- straight-line relational synthesis and conditionals -- and asserts
the recursion/operator plumbing is in place.
"""

from __future__ import annotations

import os
import subprocess
import sys

from aeon.core.terms import If, Term
from aeon.core.types import top
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.identification import get_holes_info, incomplete_functions_and_holes
from aeon.synthesis.modules.cata import CATASynthesizer
from aeon.synthesis.modules.lta.polymorphism import collect_type_universe
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from tests.driver import check_and_return_core

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _solve(code: str, budget: float = 40.0) -> Term:
    term, ctx, ectx, metadata = check_and_return_core(code)
    targets = incomplete_functions_and_holes(ctx, term)
    holes = synthesize_holes(ctx, ectx, term, targets, metadata, CATASynthesizer(), budget=budget)
    return holes[next(iter(holes))]


def _components(code: str):
    """Run CATA's component collection on a hole and return (builders, atoms)."""
    term, ctx, ectx, metadata = check_and_return_core(code)
    targets = incomplete_functions_and_holes(ctx, term)
    info = get_holes_info(ctx, term, top, targets, refined_types=True)
    hole = targets[0][1][0]
    ty, tyctx = info[hole]
    universe = collect_type_universe(tyctx, ty)
    return CATASynthesizer()._collect(tyctx, universe)


def test_factory_registers_cata():
    assert isinstance(make_synthesizer("cata"), CATASynthesizer)


def test_solves_relational_operator_hole():
    # {v:Int | v > x} is relational (mentions the parameter x). CATA builds the
    # monomorphised `+` and discharges x + 1 > x for all x.
    t = _solve("def succ (x:Int) : {v:Int | v > x} := ?hole;")
    assert "+" in str(t), str(t)


def test_solves_conditional_select():
    # Satisfiable only by a conditional: if b then x else y.
    t = _solve("def pick (b:Bool) (x:Int) (y:Int) : {v:Int | (b --> v = x) && (!b --> v = y)} := ?hole;")
    assert isinstance(t, If), str(t)
    assert "x" in str(t.then) and "y" in str(t.otherwise)


def test_solves_relational_predecessor():
    # RC-category relational comparator (Contata benchmark spirit): the relation
    # v < x pins the result below the input; CATA discharges a witness (x - 1).
    t = _solve("def pred (x:Int) : {v:Int | v < x} := ?hole;")
    assert "-" in str(t) or "+" in str(t), str(t)


def test_solves_relational_double():
    # The relation v = x + x pins the result to twice the input.
    t = _solve("def double (x:Int) : {v:Int | v = x + x} := ?hole;")
    assert "+" in str(t) or "*" in str(t), str(t)


def test_monomorphizes_polymorphic_operators():
    # The polymorphic Num/Ord operators must appear as first-order Int/Bool
    # components, otherwise no arithmetic/comparison term could be built.
    builders, _atoms = _components("def succ (x:Int) : {v:Int | v > x} := ?hole;")
    int_heads = " ".join(str(c.head) for c in builders.get("Int", []))
    bool_heads = " ".join(str(c.head) for c in builders.get("Bool", []))
    assert "(+)[Int" in int_heads and "(-)[Int" in int_heads, int_heads
    assert "(>=)[Int" in bool_heads or "(<)[Int" in bool_heads, bool_heads


def test_partial_operators_available():
    # Division and modulo are ordinary components now that the verifier handles
    # division-by-zero soundly (a candidate like -2 / 0 is rejected, not
    # vacuously accepted), so CATA no longer needs to work around it.
    builders, _atoms = _components("def succ (x:Int) : {v:Int | v > x} := ?hole;")
    heads = " ".join(str(c.head) for cs in builders.values() for c in cs)
    assert "(/)[Int" in heads, heads  # polymorphic `/` monomorphised at Int
    assert "%" in heads, heads  # monomorphic Int `%`


def test_recursive_self_call_is_a_component():
    # The function being synthesised is in scope in its own body, so the
    # recursive call is available as a component -- the basis for recursion.
    builders, _atoms = _components("def f (x:{v:Int | v >= 0}) : {v:Int | v >= x} := ?hole;")
    heads = " ".join(str(c.head) for cs in builders.values() for c in cs)
    assert "f" in heads, heads


def test_cli_runs_cata_backend():
    proc = subprocess.run(
        [
            sys.executable,
            "-m",
            "aeon",
            "--no-main",
            "-s",
            "cata",
            "--budget",
            "30",
            "examples/synthesis/cata/operator_relational.ae",
        ],
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=120,
    )
    out = proc.stdout + proc.stderr
    assert "Traceback" not in proc.stderr, out[-2000:]
    assert "?hole:" in out, out[-2000:]
