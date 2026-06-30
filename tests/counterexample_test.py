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


def test_counterexample_with_uninterpreted_function():
    """Counterexamples display values for base-type inputs even when
    uninterpreted functions are involved.

    The uninterpreted function itself won't have a concrete interpretation
    in the model, but base-type variables will have concrete values."""
    src = """
def my_measure: (x:Int) -> Int := uninterpreted;

def claim_positive (n:{v:Int | v >= 0}) : {r:Int | r >= 0} :=
    n - 10;
"""
    err = _liquid_failure(src)
    cex = err.counterexample()
    # This should produce a counterexample because n - 10 is not always >= 0
    # when n >= 0 (e.g., n=5 gives -5)
    assert cex is not None
    assert "n =" in cex
    # The counterexample should show a small non-negative value for n
    pairs = model_for_invalid(err.vc)
    assert pairs is not None
    values = dict(pairs)
    n_key = next(k for k in values if k.startswith("n"))
    n_val = int(values[n_key])
    # n should be >= 0 (the precondition) but n - 10 < 0, so 0 <= n < 10
    assert 0 <= n_val < 10


def test_counterexample_with_polymorphic_uninterpreted():
    """Counterexamples with polymorphic uninterpreted functions on base types."""
    src = """
def my_len : forall a:B, (x: a) -> Int := uninterpreted

def bad_double (n: {v:Int | v >= 0}) : {r: Int | r >= n + 10} :=
    n + n ;
"""
    err = _liquid_failure(src)
    cex = err.counterexample()
    assert cex is not None
    assert "counterexample:" in str(err)
    # Should show the value of n that makes the postcondition false
    assert "n =" in cex
    # n should be small (0-9) since n + n < n + 10 when n < 10
    pairs = model_for_invalid(err.vc)
    assert pairs is not None
    values = dict(pairs)
    n_key = next((k for k in values if "n" in k.lower()), None)
    if n_key:
        n_val = int(values[n_key])
        assert 0 <= n_val < 10


def test_counterexample_with_custom_sort_constructor():
    """Custom sort values may appear as opaque witnesses in counterexamples.

    When Z3 needs to produce a counterexample involving custom sorts, it
    creates opaque witness values. The counterexample shows both base-type
    values (Int, Float, etc.) and these opaque sort values."""
    src = """
type Tree;
def tree_make : Tree := native "None";

def bad_check (n:{v:Int | v >= 0}) : {r:Int | r >= n + 5} :=
    n;
"""
    err = _liquid_failure(src)
    cex = err.counterexample()
    # This should produce a counterexample because n >= n + 5 is false
    assert cex is not None
    assert "n =" in cex
    pairs = model_for_invalid(err.vc)
    assert pairs is not None
    # n should be a concrete Int value
    values = dict(pairs)
    assert any("n" in k.lower() for k in values)
