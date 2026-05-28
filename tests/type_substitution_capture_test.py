"""Capture-avoidance tests for `type_substitution`.

If a binder shadows a name that appears free in the substituted term, naive
substitution would capture: the previously-free variable becomes bound by
the shadowing binder. Proper substitution avoids this (typically by
alpha-renaming the binder).

Tracked by issue #286 — currently expected to fail.
"""

import pytest

from aeon.core.types import Kind
from aeon.elaboration.instantiation import type_substitution
from aeon.sugar.stypes import (
    SAbstractionType,
    STypePolymorphism,
    STypeVar,
)
from aeon.utils.name import Name


@pytest.mark.xfail(reason="capture-avoidance not implemented; see issue #286", strict=True)
def test_type_polymorphism_capture():
    """ty = forall X:B. a   ;  substitute a -> X.
    Naive result: forall X:B. X  (the previously-free X is captured).
    Correct: the body's X must remain free (binder gets a fresh name)."""
    X = Name("X", 0)
    a = Name("a", 0)
    ty = STypePolymorphism(X, Kind.BASE, STypeVar(a))
    beta = STypeVar(X)

    result = type_substitution(ty, a, beta)

    assert isinstance(result, STypePolymorphism)
    bound_name = result.name
    body = result.body
    assert isinstance(body, STypeVar)
    # The free X (substituted in) must NOT have been captured by the binder.
    assert bound_name != body.name, (
        f"Variable capture: outer binder {bound_name} captured the free X "
        f"that was substituted into the body. Result: {result}"
    )


@pytest.mark.xfail(reason="capture-avoidance not implemented; see issue #286", strict=True)
def test_abstraction_type_capture():
    """ty = (x:Int) -> a  with parameter named after the to-be-substituted target.

    Substitute a -> <something mentioning x's name>. The body's reference must
    remain free.
    """
    # ty = forall X. (X -> a)   substitute a -> X
    X = Name("X", 0)
    a = Name("a", 0)
    arrow = SAbstractionType(Name("p", 0), STypeVar(X), STypeVar(a))
    ty = STypePolymorphism(X, Kind.BASE, arrow)
    beta = STypeVar(X)

    result = type_substitution(ty, a, beta)
    assert isinstance(result, STypePolymorphism)
    # Look inside: result = forall X'. (X' -> X)   if alpha-renamed
    # Or:         result = forall X. (X -> X)     if captured
    outer_name = result.name
    inner = result.body
    assert isinstance(inner, SAbstractionType)
    assert isinstance(inner.var_type, STypeVar)
    assert isinstance(inner.type, STypeVar)
    return_x = inner.type.name
    # The X substituted in (return position) should NOT equal the outer binder.
    assert outer_name != return_x, (
        f"Variable capture in arrow type: outer binder {outer_name} now binds "
        f"the X that was supposed to remain free. Result: {result}"
    )
