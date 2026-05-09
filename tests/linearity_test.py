"""Phase 2a — linearity (QTT) enforcement.

These tests check the syntactic-occurrence linearity pass that runs after
the existing constraint check. They cover:

- ``ω``-bound names (the default for every existing program) are
  unaffected, regardless of how often they appear.
- ``1``-bound names (linear) must appear exactly once in their scope.
- ``0``-bound names (erased) must not appear at all.
- ``if`` branches with a ``1``-bound name must consume it equally.
- Errors thread through ``check_type_errors`` after the constraint
  check, so the user sees both kinds of diagnostic in one go.
"""

from __future__ import annotations

from aeon.core.bind import bind_ids
from aeon.core.types import top
from aeon.elaboration import elaborate
from aeon.facade.api import (
    ErasedUsedAtRuntimeError,
    LinearBranchMismatchError,
    LinearUnusedError,
    LinearUsedTooManyTimesError,
)
from aeon.sugar.desugar import desugar
from aeon.sugar.lowering import lower_to_core, lower_to_core_context
from aeon.sugar.parser import parse_program
from aeon.typechecking.linearity import check_linearity
from aeon.typechecking.typeinfer import check_type_errors


def _typecheck(source: str):
    prog = parse_program(source)
    desugared = desugar(prog, is_main_hole=False)
    sterm = elaborate(desugared.elabcontext, desugared.program)
    core = lower_to_core(sterm)
    typing_ctx = lower_to_core_context(desugared.elabcontext)
    typing_ctx, core = bind_ids(typing_ctx, core)
    return list(check_type_errors(typing_ctx, core, top))


def _linearity(source: str):
    prog = parse_program(source)
    desugared = desugar(prog, is_main_hole=False)
    sterm = elaborate(desugared.elabcontext, desugared.program)
    core = lower_to_core(sterm)
    typing_ctx = lower_to_core_context(desugared.elabcontext)
    typing_ctx, core = bind_ids(typing_ctx, core)
    return check_linearity(core)


def _evaluate(source: str):
    """Lower, type-check, and run a program. Returns ``main``'s result."""
    from aeon.backend.evaluator import EvaluationContext, eval as backend_eval
    from aeon.prelude.prelude import evaluation_vars

    prog = parse_program(source)
    desugared = desugar(prog, is_main_hole=False)
    sterm = elaborate(desugared.elabcontext, desugared.program)
    core = lower_to_core(sterm)
    typing_ctx = lower_to_core_context(desugared.elabcontext)
    typing_ctx, core = bind_ids(typing_ctx, core)
    ctx = EvaluationContext(evaluation_vars)
    return backend_eval(core, ctx)


# ---------------------------------------------------------------------------
# Sanity / no-op cases
# ---------------------------------------------------------------------------


def test_omega_default_no_check():
    """Programs without any multiplicity annotation aren't flagged."""
    src = """
def main (i: Int) : Int =
    let a = 5 in
    a + a;
"""
    errs = _linearity(src)
    assert errs == [], f"expected no linearity errors, got {errs}"


def test_omega_explicit_no_check():
    """Explicit ``omega`` matches the default — no enforcement."""
    src = """
def main (i: Int) : Int =
    let omega a = 5 in
    a + a;
"""
    errs = _linearity(src)
    assert errs == [], f"expected no linearity errors, got {errs}"


# ---------------------------------------------------------------------------
# Linear (μ = 1) — must use exactly once
# ---------------------------------------------------------------------------


def test_linear_used_exactly_once_ok():
    src = """
def main (i: Int) : Int =
    let 1 a = 5 in
    a;
"""
    errs = _linearity(src)
    assert errs == [], f"expected no errors, got {errs}"


def test_linear_unused_errors():
    src = """
def main (i: Int) : Int =
    let 1 a = 5 in
    42;
"""
    errs = _linearity(src)
    assert any(isinstance(e, LinearUnusedError) for e in errs), errs


def test_linear_used_twice_errors():
    src = """
def main (i: Int) : Int =
    let 1 a = 5 in
    a + a;
"""
    errs = _linearity(src)
    assert any(isinstance(e, LinearUsedTooManyTimesError) for e in errs), errs


# ---------------------------------------------------------------------------
# Erased (μ = 0) — must not be used at runtime
# ---------------------------------------------------------------------------


def test_erased_unused_ok():
    src = """
def main (i: Int) : Int =
    let 0 a = 5 in
    42;
"""
    errs = _linearity(src)
    assert errs == [], f"expected no errors, got {errs}"


def test_erased_used_errors():
    src = """
def main (i: Int) : Int =
    let 0 a = 5 in
    a;
"""
    errs = _linearity(src)
    assert any(isinstance(e, ErasedUsedAtRuntimeError) for e in errs), errs


# ---------------------------------------------------------------------------
# Branches must consume linear names equally
# ---------------------------------------------------------------------------


def test_linear_used_equally_in_branches_ok():
    src = """
def main (i: Int) : Int =
    let 1 a = 5 in
    if i > 0 then a else a;
"""
    errs = _linearity(src)
    assert errs == [], f"expected no errors, got {errs}"


def test_linear_used_in_only_one_branch_errors():
    """`if c then a else 0` uses a linearly only in one branch — but the
    syntactic-count check sees two occurrences (one per arm) and flags
    a branch-mismatch error rather than too-many-uses."""
    src = """
def main (i: Int) : Int =
    let 1 a = 5 in
    if i > 0 then a else 0;
"""
    errs = _linearity(src)
    # Either flavour of error is acceptable evidence that the program
    # was rejected; we want at least one linearity error.
    assert any(
        isinstance(e, (LinearBranchMismatchError, LinearUsedTooManyTimesError, LinearUnusedError)) for e in errs
    ), errs


# ---------------------------------------------------------------------------
# Plumbing through `check_type_errors`
# ---------------------------------------------------------------------------


def test_linearity_errors_surface_through_check_type_errors():
    src = """
def main (i: Int) : Int =
    let 1 a = 5 in
    a + a;
"""
    errs = _typecheck(src)
    assert any(isinstance(e, LinearUsedTooManyTimesError) for e in errs), errs


def test_omega_program_typecheck_is_clean():
    """A vanilla, multiplicity-free program produces no errors of any kind."""
    src = """
def f (n: Int) : Int = n + 1;

def main (i: Int) : Int =
    let a = 5 in
    f a;
"""
    errs = _typecheck(src)
    assert errs == [], f"expected clean typecheck, got {errs}"


# ---------------------------------------------------------------------------
# Realistic file-handle pattern (the original motivating example)
# ---------------------------------------------------------------------------


def test_linear_file_handle_close_ok():
    """`let 1 f = open in close f` is the canonical "must be closed" pattern.

    Under QTT scaling, ``close_f`` must declare its parameter linear so the
    obligation transfers; if it took an ω parameter the linear ``f`` would
    be scaled to ω in ``close_f f`` and rejected."""
    src = """
def open_f (path: Int) : Int = path;
def close_f (1 f: Int) : Int = f;

def main (i: Int) : Int =
    let 1 f = open_f 0 in
    close_f f;
"""
    errs = _typecheck(src)
    # No linearity errors expected. Other constraint errors (if any) are
    # incidental to this test, so we only assert there are no linearity
    # errors in particular.
    from aeon.facade.api import LinearityError

    lin = [e for e in errs if isinstance(e, LinearityError)]
    assert lin == [], f"expected no linearity errors, got {lin}"


def test_linear_file_handle_unclosed_errors():
    """Forgetting the `close` produces a `LinearUnusedError`."""
    src = """
def open_f (path: Int) : Int = path;

def main (i: Int) : Int =
    let 1 f = open_f 0 in
    42;
"""
    errs = _typecheck(src)
    assert any(isinstance(e, LinearUnusedError) for e in errs), errs


def test_linear_file_handle_double_close_errors():
    """Closing twice produces a `LinearUsedTooManyTimesError`."""
    src = """
def open_f (path: Int) : Int = path;
def close_f (1 f: Int) : Int = f;

def main (i: Int) : Int =
    let 1 f = open_f 0 in
    close_f f + close_f f;
"""
    errs = _typecheck(src)
    assert any(isinstance(e, LinearUsedTooManyTimesError) for e in errs), errs


# ---------------------------------------------------------------------------
# QTT scaling — parameter multiplicity multiplies the argument's tally
# ---------------------------------------------------------------------------


def test_linear_passed_to_omega_param_errors():
    """Passing a ``1``-bound value into an ``ω``-parameter scales the
    argument tally to ``ω``, breaking the linear obligation. The
    syntactic-count check from Phase 2a missed this; Phase 2b catches it."""
    src = """
def use_anyhow (x: Int) : Int = 0;

def main (i: Int) : Int =
    let 1 a = 5 in
    use_anyhow a;
"""
    errs = _linearity(src)
    assert any(isinstance(e, LinearUsedTooManyTimesError) for e in errs), errs


def test_linear_passed_to_linear_param_ok():
    """Passing a ``1``-bound value into a ``1``-parameter transfers the
    obligation cleanly: ``1 ⊗ 1 = 1``."""
    src = """
def consume (1 x: Int) : Int = x;

def main (i: Int) : Int =
    let 1 a = 5 in
    consume a;
"""
    errs = _linearity(src)
    assert errs == [], f"expected no linearity errors, got {errs}"


def test_omega_passed_to_linear_param_ok():
    """Calling a linear-parameter function with an unrestricted value is
    fine — the parameter's linear obligation is local to the function."""
    src = """
def consume (1 x: Int) : Int = x;

def main (i: Int) : Int =
    let a = 5 in
    consume a;
"""
    errs = _linearity(src)
    assert errs == [], f"expected no linearity errors, got {errs}"


def test_erased_passed_to_omega_param_errors():
    """A ``0``-bound name leaking into a runtime application — even
    through an ``ω``-parameter — is a runtime use of an erased binding."""
    src = """
def use_anyhow (x: Int) : Int = 0;

def main (i: Int) : Int =
    let 0 a = 5 in
    use_anyhow a;
"""
    errs = _linearity(src)
    assert any(isinstance(e, ErasedUsedAtRuntimeError) for e in errs), errs


def test_erased_scaled_through_zero_param_ok():
    """``0 ⊗ μ = 0`` — a ``0``-parameter erases its argument's tally, so
    even passing a ``0``-bound name is fine."""
    src = """
def ignore (0 x: Int) : Int = 0;

def main (i: Int) : Int =
    let 0 a = 5 in
    ignore a;
"""
    errs = _linearity(src)
    assert errs == [], f"expected no linearity errors, got {errs}"


# ---------------------------------------------------------------------------
# Phase 3 — alias-aware tally projection
# ---------------------------------------------------------------------------


def test_alias_then_double_use_caught():
    """`let g = f` aliases `f` as `g`. Using `g` twice (via a linear-param
    function applied twice) should still consume `f` twice and trip the
    linear binder. Without alias projection the tally for `f` stayed at 1
    and the violation was missed."""
    src = """
def close_f (1 f: Int) : Int = f;

def main (i: Int) : Int =
    let 1 f = 5 in
    let g = f in
    close_f g + close_f g;
"""
    errs = _linearity(src)
    assert any(isinstance(e, LinearUsedTooManyTimesError) for e in errs), errs


def test_alias_then_use_via_alias_only_ok():
    """`let g = f in close_f g` — `f` is used once via the alias, which is
    its single linear use. Should pass."""
    src = """
def close_f (1 f: Int) : Int = f;

def main (i: Int) : Int =
    let 1 f = 5 in
    let g = f in
    close_f g;
"""
    errs = _linearity(src)
    assert errs == [], f"expected no errors, got {errs}"


def test_alias_chain_used_too_many():
    """Aliasing through multiple `let`s should still propagate to the
    original linear binder."""
    src = """
def close_f (1 f: Int) : Int = f;

def main (i: Int) : Int =
    let 1 f = 5 in
    let g = f in
    let h = g in
    close_f h + close_f h;
"""
    errs = _linearity(src)
    assert any(isinstance(e, LinearUsedTooManyTimesError) for e in errs), errs


def test_alias_then_use_original_after_consume():
    """Using both the alias *and* the original name counts as two uses of
    the original linear binder."""
    src = """
def close_f (1 f: Int) : Int = f;

def main (i: Int) : Int =
    let 1 f = 5 in
    let g = f in
    close_f g + close_f f;
"""
    errs = _linearity(src)
    assert any(isinstance(e, LinearUsedTooManyTimesError) for e in errs), errs


# ---------------------------------------------------------------------------
# Multiplicity polymorphism — `(n x: T)` works for any caller mult
# ---------------------------------------------------------------------------


def test_n_arg_accepts_linear_value():
    """``(n x: T)`` is the identity on the caller side, so a linear value
    flows through without being consumed by the function."""
    src = """
def take_n (n x: Int) : Int = x;

def main (i: Int) : Int =
    let 1 a = 5 in
    take_n a;
"""
    errs = _linearity(src)
    assert errs == [], f"expected no errors, got {errs}"


def test_n_arg_accepts_omega_value():
    """``n`` works for ω callers too — scaling by ``n`` is identity."""
    src = """
def take_n (n x: Int) : Int = x;

def main (i: Int) : Int =
    let a = 5 in
    take_n a;
"""
    errs = _linearity(src)
    assert errs == [], f"expected no errors, got {errs}"


def test_n_arg_body_check_is_skipped():
    """A polymorphic-multiplicity binder doesn't enforce body-side use
    discipline, so an unused parameter doesn't error."""
    src = """
def discard (n x: Int) : Int = 0;

def main (i: Int) : Int = discard 0;
"""
    errs = _linearity(src)
    assert errs == [], f"expected no errors, got {errs}"


def test_n_arg_body_can_use_param_many_times():
    """``n`` says nothing about how the body uses the parameter — twice is
    fine, just like ω."""
    src = """
def double (n x: Int) : Int = x + x;

def main (i: Int) : Int =
    let 1 a = 5 in
    double a;
"""
    errs = _linearity(src)
    assert errs == [], f"expected no errors, got {errs}"


# ---------------------------------------------------------------------------
# Native FFI bottom — opaque bodies satisfy any declared multiplicity
# ---------------------------------------------------------------------------


def test_native_ffi_with_linear_param_ok():
    """A function whose body is ``native "..."`` can declare any
    multiplicity — the body's tally produces ``_Bottom`` for every name in
    scope so the binder check passes."""
    src = """
def write (1 buf: Int) : Int = native "buf";

def main (i: Int) : Int =
    let 1 b = 5 in
    write b;
"""
    errs = _linearity(src)
    assert errs == [], f"expected no errors, got {errs}"


def test_native_ffi_with_erased_param_ok():
    """``(0 x: T)`` on a native body is fine: the body never references
    ``x`` syntactically (it's inside an opaque string), and ``_Bottom``
    satisfies the erased discipline."""
    src = """
def ghost (0 x: Int) : Int = native "0";

def main (i: Int) : Int = ghost 0;
"""
    errs = _linearity(src)
    assert errs == [], f"expected no errors, got {errs}"


# ---------------------------------------------------------------------------
# Match / inductive destructuring — handler binders inherit the
# constructor's parameter multiplicities
# ---------------------------------------------------------------------------


def test_match_linear_constructor_binders_used_linearly_ok():
    """An inductive constructor declared ``(1 a) (1 b)`` makes the
    corresponding match-handler binders linear. Using each exactly once
    in the branch body is fine."""
    src = """
inductive LinPair
| pair (1 a: Int) (1 b: Int) : LinPair

def consume (1 x: Int) (1 y: Int) : Int = x + y;

def main (args: Int) : Int =
    let p : LinPair = LinPair_pair 1 2 in
    match p with
    | pair x y => consume x y;
"""
    errs = _linearity(src)
    assert errs == [], f"expected no errors, got {errs}"


def test_match_linear_constructor_binders_double_use_errors():
    """Using a linear-constructor binder more than once in the match
    branch body trips the linear binder check."""
    src = """
inductive LinPair
| pair (1 a: Int) (1 b: Int) : LinPair

def consume (1 x: Int) (1 y: Int) : Int = x + y;

def main (args: Int) : Int =
    let p : LinPair = LinPair_pair 1 2 in
    match p with
    | pair x y => consume x x;
"""
    errs = _linearity(src)
    assert any(isinstance(e, LinearUsedTooManyTimesError) for e in errs), errs


def test_match_omega_constructor_binders_unaffected():
    """Constructors without multiplicity annotations behave the same as
    before — handlers default to ``ω`` and the body is unconstrained."""
    src = """
inductive Pair
| pair (a: Int) (b: Int) : Pair

def main (args: Int) : Int =
    let p : Pair = Pair_pair 1 2 in
    match p with
    | pair x y => x + x + y;
"""
    errs = _linearity(src)
    assert errs == [], f"expected no errors, got {errs}"


def test_native_ffi_caller_still_respects_declared_mult():
    """Even though the body is opaque, the caller-side QTT scaling still
    fires from the declared multiplicity. Passing a linear value into an
    ``ω``-parameter native shim scales to ω and trips the linear binder."""
    src = """
def use_anyhow (x: Int) : Int = native "x";

def main (i: Int) : Int =
    let 1 a = 5 in
    use_anyhow a;
"""
    errs = _linearity(src)
    assert any(isinstance(e, LinearUsedTooManyTimesError) for e in errs), errs


# ---------------------------------------------------------------------------
# Phase 4 — runtime erasure: M0 bindings are not evaluated
# ---------------------------------------------------------------------------


def test_m0_let_val_is_not_evaluated_at_runtime():
    """A ``0``-bound let's value is skipped at runtime — even a value
    that would crash if executed is harmless because the binding is
    purely compile-time."""
    src = """
def main (i: Int) : Int =
    let 0 ghost : Int = native "1/0" in
    42;
"""
    assert _evaluate(src) == 42


def test_m0_rec_val_is_not_evaluated_at_runtime():
    """Same erasure for ``Rec``: an erased recursive definition's body
    is never evaluated."""
    src = """
def main (i: Int) : Int =
    let 0 ghost : Int = native "(_ for _ in iter(int, 1))[0]" in
    7;
"""
    assert _evaluate(src) == 7


def test_omega_let_val_is_evaluated():
    """The companion check: an unrestricted (default) let's value *is*
    evaluated, so a crashing native body propagates the exception."""
    import pytest

    src = """
def main (i: Int) : Int =
    let ghost : Int = native "1/0" in
    42;
"""
    with pytest.raises(ZeroDivisionError):
        _evaluate(src)
