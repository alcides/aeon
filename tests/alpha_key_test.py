"""Regression tests for ``alpha_key`` (the SMT-cache canonical key).

``alpha_key`` keys ``_smt_valid_cache``: if two *non*-equivalent constraints
ever collided on a key, a cached validity verdict would be served for the wrong
obligation -- an unsoundness. These tests pin the two properties that matter:

  1. alpha-equivalent constraints (differing only in fresh binder ids) share a key;
  2. structurally different constraints do not.

They also exercise the binder save/restore path introduced when ``_alpha_bind``
moved from copy-on-bind to a mutable env with explicit unbind: shadowing and
sibling scopes must not leak a binding past its subtree.
"""

from __future__ import annotations

from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt, LiquidVar
from aeon.core.types import t_int
from aeon.utils.name import Name
from aeon.verification.vcs import (
    Conjunction,
    Implication,
    LiquidConstraint,
    ReflectedFunctionDeclaration,
    alpha_key,
)


def _gt(name: Name, k: int) -> LiquidApp:
    """The liquid term ``name > k``."""
    return LiquidApp(Name(">", 0), [LiquidVar(name), LiquidLiteralInt(k)])


def _forall(name: Name, body) -> Implication:
    """``∀name:Int, (True) => body``."""
    return Implication(name, t_int, LiquidLiteralBool(True), body)


def test_alpha_key_is_deterministic():
    x = Name("x", 1)
    c = _forall(x, LiquidConstraint(_gt(x, 0)))
    assert alpha_key(c) == alpha_key(c)


def test_fresh_ids_collapse_to_same_key():
    # Same constraint shape, different fresh ids on the bound variable.
    a = _forall(Name("x", 1), LiquidConstraint(_gt(Name("x", 1), 0)))
    b = _forall(Name("x", 99), LiquidConstraint(_gt(Name("x", 99), 0)))
    assert alpha_key(a) == alpha_key(b)


def test_binder_name_is_preserved_in_key():
    # Only the volatile fresh *id* is normalized; the binder *name* is kept.
    # Differing names therefore yield differing keys -- always safe (it can only
    # reduce cache sharing, never alias two distinct obligations onto one key).
    a = _forall(Name("x", 1), LiquidConstraint(_gt(Name("x", 1), 0)))
    b = _forall(Name("y", 1), LiquidConstraint(_gt(Name("y", 1), 0)))
    assert alpha_key(a) != alpha_key(b)


def test_distinct_refinements_differ():
    x = Name("x", 1)
    gt = _forall(x, LiquidConstraint(_gt(x, 0)))
    ge = _forall(x, LiquidConstraint(LiquidApp(Name(">=", 0), [LiquidVar(x), LiquidLiteralInt(0)])))
    assert alpha_key(gt) != alpha_key(ge)


def test_free_variable_kept_distinct_from_bound():
    # A free variable must not normalize like a bound one.
    x = Name("x", 1)
    bound = _forall(x, LiquidConstraint(_gt(x, 0)))
    free = LiquidConstraint(_gt(Name("x", 1), 0))
    assert alpha_key(bound) != alpha_key(free)


def test_shadowing_is_unwound_on_scope_exit():
    """Outer binds x; an inner binder shadows it; the trailing sibling
    reference must resolve back to the *outer* x once the inner scope exits.

    With the mutable-env binder, a missing unbind would leave the inner id in
    scope, so the trailing reference would alias the inner binding instead of
    the outer one. We assert both resolutions appear with their distinct ids."""
    x = Name("x", 1)
    inner = _forall(x, LiquidConstraint(_gt(x, 0)))  # inner ∀x, ... (x>0)
    trailing = LiquidConstraint(_gt(x, 0))  # x>0 in the OUTER scope
    outer = _forall(x, Conjunction(inner, trailing))
    key = alpha_key(outer)
    # outer x -> #0, inner x -> #1 (shadow). The inner body reads #1; the
    # trailing sibling, after the inner scope is unwound, reads the outer #0.
    assert "(x#1 > 0)" in key, key  # inner reference
    assert "(x#0 > 0)" in key, key  # restored outer reference (fails if unbind is broken)


def test_reflected_multiple_binders_roundtrip():
    # Multiple accumulated binders (function name + params) must each unwind.
    p = Name("p", 1)
    refl = ReflectedFunctionDeclaration(
        name=Name("f", 1),
        type=t_int,  # type slot not inspected structurally here
        params=(p,),
        body=_gt(p, 0),
        seq=LiquidConstraint(LiquidLiteralBool(True)),
    )
    # Determinism + alpha-invariance under renaming the param/function ids.
    refl2 = ReflectedFunctionDeclaration(
        name=Name("f", 7),
        type=t_int,
        params=(Name("p", 7),),
        body=_gt(Name("p", 7), 0),
        seq=LiquidConstraint(LiquidLiteralBool(True)),
    )
    assert alpha_key(refl) == alpha_key(refl2)
