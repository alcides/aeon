"""Tests for the SyMetric metric-program-synthesis backend.

SyMetric is *only* a metric synthesiser: it clusters candidates and steers
repair by the distance between their outputs. These tests check that it (a)
minimises a numeric objective and (b) fails -- with a clear message -- on holes
where that strategy does not apply: no objective, or outputs (an inductive/AST
value) that are not a space a distance can be computed on.
"""

from __future__ import annotations

import os
import subprocess
import sys

import pytest

from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.modules.symetric import SymetricSynthesizer
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from tests.driver import check_and_return_core

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _solve(code: str, budget: float = 20.0):
    term, ctx, ectx, metadata = check_and_return_core(code)
    targets = incomplete_functions_and_holes(ctx, term)
    holes = synthesize_holes(ctx, ectx, term, targets, metadata, SymetricSynthesizer(), budget=budget)
    return holes[next(iter(holes))]


def test_factory_registers_symetric():
    assert isinstance(make_synthesizer("symetric"), SymetricSynthesizer)


def test_metric_objective_is_minimised_to_zero(tmp_path):
    # A numeric objective with a numeric output: the suitable case. |target-12|
    # is driven to 0 at target == 12. Run through the CLI (the real driver) so
    # the objective and the output evaluator are wired exactly as in production.
    src = tmp_path / "min.ae"
    src.write_text(
        "def dist (x:Int) : {r:Int | r >= 0} := if x >= 12 then x - 12 else 12 - x;\n\n"
        "@minimize_int(dist target)\n"
        "def target : Int := (let dist := unit in ?hole);\n"
    )
    proc = subprocess.run(
        [sys.executable, "-m", "aeon", "--no-main", "-s", "symetric", "--budget", "10", str(src)],
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=120,
    )
    out = proc.stdout + proc.stderr
    assert "Traceback" not in proc.stderr, out[-2000:]
    assert "?hole: 12" in out, out[-2000:]


def test_rejects_hole_without_objective():
    # No @minimize/@maximize: there is no metric to cluster or steer by.
    code = "def n : {v:Int | v + 4 = 7} := ?hole;"
    with pytest.raises(SynthesisNotSuccessful, match="metric synthesiser"):
        _solve(code, budget=10.0)


def test_cluster_decorator_makes_csg_suitable():
    # With @cluster(scene shape) the candidate's clustering feature is its
    # rasterised scene (a numeric vector), so the inverse-CSG benchmark -- whose
    # raw output is an AST -- becomes suitable: symetric runs instead of
    # rejecting it.
    proc = subprocess.run(
        [
            sys.executable,
            "-m",
            "aeon",
            "--no-main",
            "-s",
            "symetric",
            "--budget",
            "8",
            "examples/synthesis/csg/csg_tiny_two_circle.ae",
        ],
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=120,
    )
    out = proc.stdout + proc.stderr
    assert "Not suitable" not in out, out[-2000:]
    assert "Traceback" not in proc.stderr, out[-2000:]


_ADT_PROGRAM = (
    "inductive List a\n"
    "| nil : {l: (List a) | len l = 0}\n"
    "| cons (hd: a) (tl: (List a)) : {l: (List a) | len l = len tl + 1}\n"
    "+ len (l: (List a)) : Int\n\n"
    "inductive Bag\n"
    "| mk_bag (xs: (List Int)) : Bag\n\n"
    "def count (xs: (List Int)) : Int :=\n"
    "    match xs with\n"
    "    | nil => 0\n"
    "    | cons h t => 1 + count t;\n\n"
    "def total (b: Bag) : Int :=\n"
    "    match b with\n"
    "    | mk_bag xs => count xs;\n\n"
    "@cluster(total new_bag)\n"
    "@maximize_int(total new_bag)\n"
    "def new_bag : Bag := (let count := unit in let total := unit in ?hole);\n"
)


def test_monomorphises_polymorphic_constructors():
    # ``List_cons``/``List_nil`` are polymorphic (``forall a``); symetric used to
    # skip them entirely, leaving any goal built from ``List Int`` (here ``Bag``)
    # unconstructible. They must now be monomorphised on demand to ``List<Int>``.
    from aeon.core.types import AbstractionType, Kind, TypeConstructor, TypePolymorphism, TypeVar, t_int
    from aeon.typechecking.context import TypingContext
    from aeon.utils.name import Name

    a = Name("a", 0)
    list_a = TypeConstructor(Name("List", 0), [TypeVar(a)])
    list_int = TypeConstructor(Name("List", 0), [t_int])
    bag = TypeConstructor(Name("Bag", 0), [])
    # List_nil : forall a. List a   ;   List_cons : forall a. a -> List a -> List a
    nil_ty = TypePolymorphism(a, Kind.BASE, list_a)
    cons_ty = TypePolymorphism(
        a, Kind.BASE, AbstractionType(Name("hd", 0), TypeVar(a), AbstractionType(Name("tl", 0), list_a, list_a))
    )
    # mk_bag : List Int -> Bag  (monomorphic; demands List Int)
    mkbag_ty = AbstractionType(Name("xs", 0), list_int, bag)
    ctx: TypingContext = TypingContext()
    for nm, ty in [(Name("List_nil", 0), nil_ty), (Name("List_cons", 0), cons_ty), (Name("Bag_mk_bag", 0), mkbag_ty)]:
        ctx = ctx.with_var(nm, ty)

    builders, atoms = SymetricSynthesizer()._collect(ctx, bag)
    assert "List<Int>" in builders, sorted(builders)
    assert "List<Int>" in atoms, sorted(atoms)
    # the cons builder carries its concrete Int instantiation as a type argument
    assert any(c.type_args for c in builders["List<Int>"])
    # and the demand is transitive: Bag's mk_bag drives the List<Int> instances
    assert any(c.name.name == "Bag_mk_bag" for c in builders.get("Bag", []))


def test_synthesises_adt_goal_with_polymorphic_lists(tmp_path):
    # End-to-end: a numeric @cluster feature makes the multi-sorted ADT goal
    # suitable, and monomorphisation lets symetric actually build (and validate)
    # a non-trivial ``Bag`` containing a ``List Int``.
    src = tmp_path / "bag.ae"
    src.write_text(_ADT_PROGRAM)
    proc = subprocess.run(
        [sys.executable, "-m", "aeon", "--no-main", "-s", "symetric", "--budget", "15", str(src)],
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=120,
    )
    out = proc.stdout + proc.stderr
    assert "Traceback" not in proc.stderr, out[-2000:]
    assert "could not build" not in out, out[-2000:]
    assert "Not suitable" not in out, out[-2000:]
    assert "Bag_mk_bag" in out, out[-2000:]


def test_rejects_non_numeric_output(tmp_path):
    # A numeric objective, but the candidate output is an inductive/AST value
    # (a Csg term) with no distance defined on it: not suitable. The CLI surfaces
    # the synthesiser's explanation and exits 2.
    src = tmp_path / "csg.ae"
    src.write_text(
        "open Shape\n\n"
        "inductive Shape\n"
        "| Box (w:Int) (h:Int) : Shape\n"
        "| Stack (a:Shape) (b:Shape) : Shape\n\n"
        'def cost (s:Shape) : Float := native "0.0";\n\n'
        "@minimize_float(cost shape)\n"
        "def shape : Shape := (let cost := unit in ?hole);\n"
    )
    proc = subprocess.run(
        [sys.executable, "-m", "aeon", "--no-main", "-s", "symetric", "--budget", "10", str(src)],
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=120,
    )
    out = proc.stdout + proc.stderr
    assert proc.returncode == 2, out[-2000:]
    assert "Not suitable" in out, out[-2000:]
    assert "numeric" in out, out[-2000:]
