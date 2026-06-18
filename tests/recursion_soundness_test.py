"""Soundness tests for well-founded recursion.

A recursive definition is typed with its declared return refinement available
for the recursive call (the inductive hypothesis). That is only sound if the
function terminates, so the termination metric must be a *well-founded* measure
— it must strictly decrease AND stay non-negative at every reachable recursive
call.

These tests pin that requirement. The NEGATIVE cases exercise recursion whose
metric decreases without a lower bound (an unbounded integer descends forever),
which must be rejected; otherwise an absurd return refinement like
``{r:Int | r > r}`` becomes inhabited and poisons downstream proofs.
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
    """Run the full front-to-typecheck pipeline; True iff no type errors.

    Mirrors the reflection-aware harness used in ``decreasing_by_test.py`` so
    reflected recursive functions get their formals bound for the SMT layer.
    """
    prog = parse_main_program(src, filename="<test>")
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
    errors = list(check_type_errors(typing_ctx, core_ast, top))
    return errors == []


# ---------------------------------------------------------------------------
# Positive: genuinely well-founded recursion must stay accepted.
# ---------------------------------------------------------------------------


def test_factorial_nat_is_accepted():
    src = """
        def fact (n:Int | n >= 0) : Int decreasing_by [n] :=
          if n = 0 then 1 else n * fact (n - 1);
        def main (_:Int) : Int := fact 5
    """
    assert _typechecks(src)


def test_explicit_recurrence_refinement_is_accepted():
    src = """
        def double (n:Int | n >= 0) : {r:Int | r = n + n} decreasing_by [n] :=
          if n = 0 then 0 else double (n - 1) + 2;
        def main (_:Int) : Int := double 5
    """
    assert _typechecks(src)


def test_inferred_metric_guarded_nat_is_accepted():
    # No explicit decreasing_by: unary Int recursion infers [n]; guarded + n>=0
    # gives a well-founded obligation.
    src = """
        def countdown (n:Int | n >= 0) : Int :=
          if n = 0 then 0 else countdown (n - 1);
        def main (_:Int) : Int := countdown 5
    """
    assert _typechecks(src)


# ---------------------------------------------------------------------------
# Negative: non-well-founded recursion must be rejected.
# ---------------------------------------------------------------------------


def test_unbounded_decrement_with_metric_is_rejected():
    # f (n-1) with metric [n] but no lower bound on n: decreases forever.
    src = """
        def f (n:Int) : Int decreasing_by [n] := f (n - 1);
        def main (_:Int) : Int := 0
    """
    assert not _typechecks(src)


def test_unbounded_decrement_inferred_metric_is_rejected():
    # Same shape, relying on the inferred [n] metric (no decreasing_by written).
    src = """
        def f (n:Int) : Int := f (n - 1);
        def main (_:Int) : Int := 0
    """
    assert not _typechecks(src)


def test_absurd_refinement_on_nonterminating_fn_is_rejected():
    # The non-terminating function claims an uninhabited codomain.
    src = """
        def f (n:Int) : {r:Int | r > r} decreasing_by [n] := f (n - 1);
        def main (_:Int) : Int := 0
    """
    assert not _typechecks(src)


def test_nonterminating_fn_cannot_poison_downstream_proof():
    # If f were accepted, binding its absurd result would let us prove `false`.
    src = """
        def f (n:Int) : {r:Int | r > r} decreasing_by [n] := f (n - 1);
        def exploit (n:Int) : {b:Bool | b} := (let x := f n in false);
        def main (_:Int) : Int := 0
    """
    assert not _typechecks(src)


def test_multiarg_no_metric_absurd_refinement_is_rejected():
    # Multi-arg recursion has no inferred metric (inference only covers the
    # unary-Int case). Without a metric, the recursive occurrence must NOT be
    # allowed to assume the declared absurd return refinement.
    src = """
        def f (n:Int) (m:Int) : {r:Int | r > r} := f n m;
        def main (_:Int) : Int := 0
    """
    assert not _typechecks(src)


def test_nonint_arg_no_metric_absurd_refinement_is_rejected():
    # A single non-Int parameter is likewise outside the inference's reach;
    # self-recursion may not assume an absurd codomain without a metric.
    src = """
        def f (b:Bool) : {r:Int | r > r} := f b;
        def main (_:Int) : Int := 0
    """
    assert not _typechecks(src)


def test_multiarg_recurrence_with_explicit_metric_is_accepted():
    # The sound escape hatch: state a well-founded metric explicitly. A
    # two-argument recursion with a guarded, decreasing first metric is total,
    # so its declared recurrence refinement may be assumed at the recursive call.
    src = """
        def add (n:Int | n >= 0) (m:Int) : {r:Int | r = n + m} decreasing_by [n] :=
          if n = 0 then m else add (n - 1) (m + 1);
        def main (_:Int) : Int := add 3 4
    """
    assert _typechecks(src)
