"""Counterexamples on refinement failures (issue #439).

When a verification condition is invalid, Z3 has a model witnessing the
failure. These tests check that the model is surfaced as a concrete,
source-level ``name = value`` counterexample on the error (used by both the
CLI and the LSP, which render errors via ``str``), and that valid programs
produce neither an error nor a spurious witness.
"""

from __future__ import annotations

from aeon.facade.api import LiquidTypeCheckingFailedRelation
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.verification.smt import model_for_invalid, render_counterexample


def _errors(source: str):
    cfg = AeonConfig(
        synthesizer="random_search",
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=0,
        no_main=True,
    )
    return list(AeonDriver(cfg).parse(aeon_code=source))


def _liquid_failure(source: str) -> LiquidTypeCheckingFailedRelation:
    errors = _errors(source)
    failures = [e for e in errors if isinstance(e, LiquidTypeCheckingFailedRelation)]
    assert failures, f"expected a liquid type-checking failure, got {errors}"
    return failures[0]


def test_counterexample_on_refinement_failure():
    # `x + x >= x` only for non-negative x, so this fails with a negative witness.
    err = _liquid_failure("def double (x:Int) : {v:Int | v >= x} := x + x ;")
    cex = err.counterexample()
    assert cex is not None
    assert "x =" in cex
    assert "counterexample:" in str(err)


def test_counterexample_witness_is_falsifying():
    # The reported `x` must actually break `x + x >= x`, i.e. be negative.
    err = _liquid_failure("def double (x:Int) : {v:Int | v >= x} := x + x ;")
    pairs = model_for_invalid(err.vc)
    assert pairs is not None
    values = dict(pairs)
    # variable names carry binder-id superscripts; find the one named `x...`.
    x_key = next(k for k in values if k.startswith("x"))
    assert int(values[x_key]) < 0


def test_counterexample_on_precondition_failure():
    src = """
    open Math
    def f (n:Int) : Float := Math.sqrt n
    def main (a:Int) : Unit := print (f a) ;
    """
    err = _liquid_failure(src)
    cex = err.counterexample()
    assert cex is not None
    assert "n =" in cex


def test_counterexample_is_memoised():
    err = _liquid_failure("def double (x:Int) : {v:Int | v >= x} := x + x ;")
    first = err.counterexample()
    assert err.counterexample() == first  # second call hits the cache


def test_valid_program_has_no_failure():
    assert not _errors("def double (x:Int) : {v:Int | v = x + x} := x + x ;")


def test_render_counterexample_consistent_with_validity():
    from aeon.verification.smt import smt_valid

    err = _liquid_failure("def double (x:Int) : {v:Int | v >= x} := x + x ;")
    # The stored VC is genuinely invalid, and the renderer produces a witness.
    assert not smt_valid(err.vc)
    assert render_counterexample(err.vc) is not None
