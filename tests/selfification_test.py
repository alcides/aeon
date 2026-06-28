"""Selfification of application results and let-fact hypotheses in
termination obligations (issue #378, options 2 and 3).

An application whose codomain is a bare base type used to synthesise an
anonymous ``{v | true}`` — no connection between the value and the call that
produced it — so facts proved *about the call* (an instantiated axiom, a
refined native's contract) could never reach obligations phrased about the
*result*. Application results are now selfified (``{v | v == f(args)}``), and
termination obligations carry the refinements of let binders on the path to
the recursive call.
"""

from __future__ import annotations

from aeon.core.bind import bind_ids
from aeon.core.types import top
from aeon.elaboration import elaborate
from aeon.sugar.ast_helpers import st_top
from aeon.sugar.bind import bind, bind_program
from aeon.sugar.desugar import DesugaredProgram, desugar
from aeon.sugar.lowering import lower_to_core, lower_to_core_context
from aeon.sugar.parser import parse_main_program
from aeon.typechecking.typeinfer import check_type_errors


def _typechecks(src: str) -> bool:
    """Full front-to-typecheck pipeline; True iff no type errors (mirrors
    ``recursion_soundness_test.py``)."""
    prog = parse_main_program(src, filename="<test>")
    prog = bind_program(prog, [])
    desugared = desugar(prog, is_main_hole=True)
    ctx, progt = bind(desugared.elabcontext, desugared.program)
    desugared = DesugaredProgram(
        progt,
        ctx,
        desugared.metadata,
        desugared.constructor_to_type,
        desugared.constructor_defs,
        desugared.inductive_decls,
        desugared.local_inductive_decls,
    )
    sterm = elaborate(desugared.elabcontext, desugared.program, st_top)
    typing_ctx = lower_to_core_context(desugared.elabcontext)
    core_ast = lower_to_core(sterm)
    typing_ctx, core_ast = bind_ids(typing_ctx, core_ast)
    errors = list(check_type_errors(typing_ctx, core_ast, top))
    return errors == []


FDIV_AXIOM = """
def fdiv : (i:Int) -> (j:Int) -> Int := fun i => fun j => native "i // j"

axiom fdiv_bounds : (i: Int) -> (j: Int) ->
    {u: Unit | (i >= 0 && j >= 2) --> (fdiv i j >= 0 && (i = 0 || fdiv i j < i))} ;
"""

FDIV_REFINED = """
def fdiv (i:{v:Int | v >= 0}) (j:{v:Int | v >= 2}) : {r:Int | r >= 0 && (i = 0 || r < i)} :=
    native "i // j"
"""


def test_axiom_fact_reaches_argument_check():
    """``fdiv n 10`` as an argument satisfies ``{v | v >= 0}`` via the axiom."""
    src = (
        FDIV_AXIOM
        + """
def needs_nat (m : {v:Int | v >= 0}) : Int := m;

def test (n : {v:Int | v >= 0}) : Int :=
    b := fdiv_bounds n 10;
    needs_nat (fdiv n 10);

def main (_:Int) : Int := test 44
"""
    )
    assert _typechecks(src)


def test_axiom_fact_reaches_let_bound_use():
    """The let-bound result stays connected to the call through selfification."""
    src = (
        FDIV_AXIOM
        + """
def needs_nat (m : {v:Int | v >= 0}) : Int := m;

def test (n : {v:Int | v >= 0}) : Int :=
    b := fdiv_bounds n 10;
    floor := fdiv n 10;
    needs_nat floor;

def main (_:Int) : Int := test 44
"""
    )
    assert _typechecks(src)


def test_axiom_fact_guards_termination_of_natural_recursion():
    """Digit-style recursion through an uninterpreted native terminates via the axiom."""
    src = (
        FDIV_AXIOM
        + """
def square_digits (n : {v:Int | v >= 0}) : Int :=
    if n = 0 then 0
    else
        b := fdiv_bounds n 10;
        d := n % 10;
        (d * d) + square_digits (fdiv n 10);

def main (_:Int) : Int := square_digits 44
"""
    )
    assert _typechecks(src)


def test_refined_native_guards_termination_via_let():
    """A refined native's contract flows through a let binder — no axiom needed."""
    src = (
        FDIV_REFINED
        + """
def count (n : {v:Int | v >= 0}) : Int :=
    if n = 0 then 0
    else
        floor := fdiv n 10;
        1 + count floor;

def main (_:Int) : Int := count 44
"""
    )
    assert _typechecks(src)


def test_fact_does_not_leak_across_branches():
    """An axiom instantiated in one branch must not justify the other branch's recursion."""
    src = (
        FDIV_AXIOM
        + """
def count (n : {v:Int | v >= 0}) : Int :=
    if n = 0 then
        b := fdiv_bounds n 10;
        0
    else
        1 + count (fdiv n 10);

def main (_:Int) : Int := count 44
"""
    )
    assert not _typechecks(src)


def test_nontermination_still_rejected():
    src = """
def loopy (n : {v:Int | v >= 0}) : Int :=
    if n = 0 then 0 else 1 + loopy n;

def main (_:Int) : Int := loopy 1
"""
    assert not _typechecks(src)
