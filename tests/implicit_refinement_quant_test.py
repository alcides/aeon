"""Unit tests for aeon.sugar.implicit_refinement_quant."""

from __future__ import annotations

import pytest

from aeon.core.types import BaseKind
from aeon.sugar.implicit_refinement_quant import (
    ImplicitRefinementQuantError,
    add_implicit_refinement_polymorphism,
    collect_free_refinement_predicate_sorts,
)
from aeon.sugar.program import SApplication, SVar
from aeon.sugar.stypes import (
    SAbstractionType,
    SRefinedType,
    SRefinementPolymorphism,
    STypeConstructor,
    STypePolymorphism,
    STypeVar,
)
from aeon.utils.name import Name


def _refined_parametric(binder: Name, base, pred: Name) -> SRefinedType:
    return SRefinedType(binder, base, SApplication(SVar(pred), SVar(binder)))


def test_collect_empty_for_plain_type():
    ty = STypeConstructor(Name("Int"), [])
    assert collect_free_refinement_predicate_sorts(ty, frozenset()) == {}


def test_collect_finds_free_predicate_sort():
    x, p = Name("x"), Name("p")
    int_ty = STypeConstructor(Name("Int"), [])
    ty = _refined_parametric(x, int_ty, p)
    got = collect_free_refinement_predicate_sorts(ty, frozenset())
    assert got == {p: int_ty}


def test_collect_respects_bound_refinement_polymorphism():
    x, p = Name("x"), Name("p")
    int_ty = STypeConstructor(Name("Int"), [])
    inner = _refined_parametric(x, int_ty, p)
    ty = SRefinementPolymorphism(p, int_ty, inner)
    assert collect_free_refinement_predicate_sorts(ty, frozenset()) == {}


def test_collect_merges_same_predicate_same_sort():
    x, y, p = Name("x"), Name("y"), Name("p")
    int_ty = STypeConstructor(Name("Int"), [])
    ty = SAbstractionType(
        Name("f"),
        _refined_parametric(x, int_ty, p),
        _refined_parametric(y, int_ty, p),
    )
    got = collect_free_refinement_predicate_sorts(ty, frozenset())
    assert got == {p: int_ty}


def test_collect_conflicting_predicate_sort_raises():
    x, y, p = Name("x"), Name("y"), Name("p")
    int_ty = STypeConstructor(Name("Int"), [])
    bool_ty = STypeConstructor(Name("Bool"), [])
    ty = SAbstractionType(
        Name("f"),
        _refined_parametric(x, int_ty, p),
        _refined_parametric(y, bool_ty, p),
    )
    with pytest.raises(ImplicitRefinementQuantError, match="conflicting domain types"):
        collect_free_refinement_predicate_sorts(ty, frozenset())


def test_collect_ignoresNameon_parametric_refinement_shape():
    """Only `p binder` (application of predicate var to the refinement binder) counts."""
    x, p = Name("x"), Name("p")
    int_ty = STypeConstructor(Name("Int"), [])
    y = Name("y")
    # p applied to y, not to x — not treated as parametric predicate on this refined type
    ref = SApplication(SVar(p), SVar(y))
    ty = SRefinedType(x, int_ty, ref)
    assert collect_free_refinement_predicate_sorts(ty, frozenset()) == {}


def test_add_implicit_wraps_top_level_free_predicate():
    x, p = Name("x"), Name("p")
    int_ty = STypeConstructor(Name("Int"), [])
    ty = SAbstractionType(Name("f"), _refined_parametric(x, int_ty, p), int_ty)
    out = add_implicit_refinement_polymorphism(ty)
    match out:
        case SRefinementPolymorphism(np, sort, body):
            assert np == p and sort == int_ty
            assert body == ty
        case _:
            pytest.fail(f"expected SRefinementPolymorphism, got {out!r}")


def test_add_implicit_under_type_forall_binds_predicate_over_t():
    t, x, p = Name("t"), Name("x"), Name("p")
    tvar = STypeVar(t)
    B = BaseKind()
    refined = _refined_parametric(x, tvar, p)
    rt = STypeConstructor(Name("Int"), [])
    body = SAbstractionType(x, refined, rt)
    ty = STypePolymorphism(t, B, body)
    out = add_implicit_refinement_polymorphism(ty)
    match out:
        case STypePolymorphism(nt, k, SRefinementPolymorphism(np, ns, inner)):
            assert nt == t and k == B and np == p and ns == tvar and inner == body
        case _:
            pytest.fail(f"unexpected shape: {out!r}")


def test_add_implicit_idempotent_when_predicate_already_quantified():
    x, p = Name("x"), Name("p")
    int_ty = STypeConstructor(Name("Int"), [])
    inner = SAbstractionType(Name("f"), _refined_parametric(x, int_ty, p), int_ty)
    ty = SRefinementPolymorphism(p, int_ty, inner)
    assert add_implicit_refinement_polymorphism(ty) == ty


def test_add_implicit_stable_order_two_predicates():
    """Wrappers nest in sorted name order: first sorted name is innermost, last is outermost."""
    x, y = Name("x"), Name("y")
    p, q = Name("p"), Name("q")
    int_ty = STypeConstructor(Name("Int"), [])
    body = SAbstractionType(
        Name("f"),
        _refined_parametric(x, int_ty, p),
        _refined_parametric(y, int_ty, q),
    )
    out = add_implicit_refinement_polymorphism(body)
    match out:
        case SRefinementPolymorphism(
            n_outer,
            s_outer,
            SRefinementPolymorphism(n_inner, s_inner, inner),
        ):
            assert (n_outer, n_inner) == (q, p)
            assert s_outer == int_ty and s_inner == int_ty
            assert inner == body
        case _:
            pytest.fail(f"expected nested SRefinementPolymorphism, got {out!r}")


def test_add_implicit_conflicting_signature_raises():
    x, y, p = Name("x"), Name("y"), Name("p")
    int_ty = STypeConstructor(Name("Int"), [])
    bool_ty = STypeConstructor(Name("Bool"), [])
    ty = SAbstractionType(
        Name("f"),
        _refined_parametric(x, int_ty, p),
        _refined_parametric(y, bool_ty, p),
    )
    with pytest.raises(ImplicitRefinementQuantError, match="conflicting domain types"):
        add_implicit_refinement_polymorphism(ty)
