"""Recursion through a refined `native` helper (issue #378).

A declared function is encoded as a bare uninterpreted SMT symbol, so the
postcondition stated by its return refinement never reached the obligation that
mentions it. A recursive function whose decreasing argument flows through a
native helper (e.g. floor division) could therefore not be verified, however
precisely the helper was specified. The fix instantiates the return-refinement
contract of a *trusted* (`native`/`uninterpreted`) function at each of its
applications.

The trust is what keeps it sound: the contract is an axiom only for a binding
whose body is never checked. A regular function's postcondition is *proven*, so
assuming it while checking that very function would be circular — pinned by the
negative cases below.
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
    """Run the full front-to-typecheck pipeline; True iff no type errors."""
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


# ---------------------------------------------------------------------------
# Positive: a precisely specified native helper makes the recursion verifiable.
# ---------------------------------------------------------------------------


def test_refined_native_enables_termination_direct_arg():
    # The decreasing argument flows directly through the native helper:
    # `count (fdiv n 10)`. `fdiv`'s return refinement supplies exactly the facts
    # the auto-inferred metric (`n`) needs: `fdiv n 10 < n` (since n != 0) and
    # `fdiv n 10 >= 0`.
    src = """
        def fdiv (i:{v:Int | v >= 0}) (j:{v:Int | v >= 2}) : {r:Int | r >= 0 && (i = 0 || r < i)} := native "i // j";
        def count (n : {v:Int | v >= 0}) : Int :=
            if n = 0 then 0 else 1 + count (fdiv n 10);
        def main (x:Int) : Int := count 100
    """
    assert _typechecks(src)


def test_refined_native_enables_termination_let_bound():
    # The same fact must reach the obligation when the result is let-bound and
    # the recursion is on the binder.
    src = """
        def fdiv (i:{v:Int | v >= 0}) (j:{v:Int | v >= 2}) : {r:Int | r >= 0 && (i = 0 || r < i)} := native "i // j";
        def count (n : {v:Int | v >= 0}) : Int :=
            if n = 0 then 0 else (floor := fdiv n 10; 1 + count floor);
        def main (x:Int) : Int := count 100
    """
    assert _typechecks(src)


def test_refined_native_postcondition_reaches_argument_subtyping():
    # The postcondition must also discharge an argument-refinement subtyping
    # check, not only a termination obligation.
    src = """
        def fdiv (i:{v:Int | v >= 0}) (j:{v:Int | v >= 2}) : {r:Int | r >= 0 && (i = 0 || r < i)} := native "i // j";
        def needs_nat (m : {v:Int | v >= 0}) : Int := m;
        def test (n : {v:Int | v >= 0}) : Int := needs_nat (fdiv n 10);
        def main (x:Int) : Int := test 5
    """
    assert _typechecks(src)


def test_uninterpreted_axiom_instantiation_reaches_subtyping():
    # The ghost-axiom idiom (issue #378, manifestation 2): an `axiom`-declared
    # fact instantiated at the call site flows into the argument check.
    src = """
        def fdiv : (i:Int) -> (j:Int) -> Int := uninterpreted;
        axiom fdiv_bounds : (i: Int) -> (j: Int) ->
            {u: Unit | (i >= 0 && j >= 2) --> (fdiv i j >= 0 && (i = 0 || fdiv i j < i))} ;
        def needs_nat (m : {v:Int | v >= 0}) : Int := m;
        def test (n : {v:Int | v >= 0}) : Int :=
            b := fdiv_bounds n 10;
            needs_nat (fdiv n 10);
        def main (x:Int) : Int := test 5
    """
    assert _typechecks(src)


# ---------------------------------------------------------------------------
# Negative: soundness must be preserved. A native too weakly specified to imply
# the decrease, and the circularity that trust-gating exists to prevent.
# ---------------------------------------------------------------------------


def test_unspecified_native_does_not_terminate():
    # No useful return refinement: nothing implies `fdiv n 10 < n`, so the
    # termination obligation must remain unprovable.
    src = """
        def fdiv (i:Int) (j:Int) : Int := native "i // j";
        def count (n : {v:Int | v >= 0}) : Int :=
            if n = 0 then 0 else 1 + count (fdiv n 10);
        def main (x:Int) : Int := count 100
    """
    assert not _typechecks(src)


def test_native_refinement_too_weak_for_decrease():
    # `r >= 0` alone does not imply `r < i`: the decrease still fails.
    src = """
        def fdiv (i:{v:Int | v >= 0}) (j:{v:Int | v >= 2}) : {r:Int | r >= 0} := native "i // j";
        def count (n : {v:Int | v >= 0}) : Int :=
            if n = 0 then 0 else 1 + count (fdiv n 10);
        def main (x:Int) : Int := count 100
    """
    assert not _typechecks(src)


def test_regular_function_postcondition_not_assumed_circularly():
    # `x` does not satisfy `{v:Int | v > x}`. A regular function is NOT trusted:
    # its own postcondition must not be assumed while checking its body (which
    # would make `x > x` vacuously provable). Contrast with a native, whose
    # contract is axiomatic.
    src = """
        def succ (x:Int) : {v:Int | v > x} := x;
        def main (a:Int) : Int := succ 3
    """
    assert not _typechecks(src)
