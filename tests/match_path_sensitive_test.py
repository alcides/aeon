"""Path-sensitive ``match``: each branch should be checked under the matched
constructor's refinement (specialised to the scrutinee).

Surface ``match`` lowers to the generated ``<T>_rec`` eliminator. With a
*non-dependent* motive the case bodies learn nothing about which constructor was
matched, so a function whose refined return type depends on the scrutinee's
constructor cannot be verified. These tests pin the desired behaviour: the
constructor's refinement (a measure fact, the only thing aeon's SMT logic models
about a datatype) must reach the branch body as a hypothesis.
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


def _type_errors(src: str) -> list:
    prog = parse_main_program(src, filename="<path-sensitive-test>")
    prog = bind_program(prog, [])
    desugared = desugar(prog, is_main_hole=True)
    ctx, progt = bind(desugared.elabcontext, desugared.program)
    desugared = DesugaredProgram(
        progt, ctx, desugared.metadata, desugared.constructor_to_type, desugared.constructor_defs
    )
    sterm = elaborate(desugared.elabcontext, desugared.program, st_top)
    typing_ctx = lower_to_core_context(desugared.elabcontext)
    core_ast = lower_to_core(sterm)
    typing_ctx, core_ast = bind_ids(typing_ctx, core_ast)
    return list(check_type_errors(typing_ctx, core_ast, top))


# A two-constructor datatype whose constructors pin the measure ``val`` to a
# distinct literal. Both branch obligations discharge from the constructor's
# measure value alone (no non-negativity reasoning needed), so this isolates
# path-sensitivity from any measure-axiom concerns.
_BIT = """
inductive Bit
| off : {b: Bit | val b = 0}
| on : {b: Bit | val b = 1}
+ val (b: Bit) : Int
"""


def test_match_branch_sees_constructor_refinement() -> None:
    """``isOn`` is correct only if each branch knows ``val x`` for that constructor."""
    src = (
        _BIT
        + """
def isOn (x: Bit) : {r: Bool | r = (val x = 1)} :=
    match x with
    | off => false
    | on => true

def main (args: Int) : Int := 0
"""
    )
    errors = _type_errors(src)
    assert errors == [], f"path-sensitive match should typecheck, got: {errors}"


def test_match_branch_refinement_is_sound() -> None:
    """The *wrong* body must still be rejected: assuming ``val x = 0`` in the
    ``off`` branch does not let us prove a false claim about the ``on`` branch."""
    src = (
        _BIT
        + """
def wrong (x: Bit) : {r: Bool | r = (val x = 1)} :=
    match x with
    | off => true
    | on => false

def main (args: Int) : Int := 0
"""
    )
    errors = _type_errors(src)
    assert errors != [], "an incorrect match body must be rejected"


def test_match_branch_constructor_field_refinement() -> None:
    """A constructor *with a field* exposes its field-dependent refinement to
    the branch: ``wrap n`` pins ``unwrap w = n``, so ``get`` returns ``n``."""
    src = """
inductive Wrap
| wrap (k: Int) : {w: Wrap | unwrap w = k}
+ unwrap (w: Wrap) : Int

def get (w: Wrap) : {r: Int | r = unwrap w} :=
    match w with
    | wrap n => n

def main (args: Int) : Int := 0
"""
    errors = _type_errors(src)
    assert errors == [], f"field-dependent constructor refinement should typecheck, got: {errors}"


def test_match_branch_field_refinement_is_sound() -> None:
    """The injected fact must not over-accept: a ``succ`` branch only knows
    ``tonat n = tonat p + 1`` for an *arbitrary* ``p``, so claiming
    ``tonat n = 1`` for every ``succ`` is rejected (it would need ``tonat p = 0``)."""
    src = """
inductive Nat2
| z : {n: Nat2 | tonat n = 0}
| s (p: Nat2) : {n: Nat2 | tonat n = tonat p + 1}
+ tonat (n: Nat2) : Int

def bad (n: Nat2) : {r: Bool | r = (tonat n = 1)} :=
    match n with
    | z => false
    | s p => true

def main (args: Int) : Int := 0
"""
    errors = _type_errors(src)
    assert errors != [], "a field-dependent claim true only for one constructor value must be rejected"
