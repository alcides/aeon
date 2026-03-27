from __future__ import annotations

from aeon.sugar.program import SApplication, STerm, SVar
from aeon.sugar.stypes import (
    SAbstractionType,
    SRefinedType,
    SRefinementPolymorphism,
    SType,
    STypeConstructor,
    STypePolymorphism,
    STypeVar,
)
from aeon.utils.name import Name


class ImplicitRefinementQuantError(Exception):
    pass


def _parametric_predicate_name(ref: STerm, binder: Name) -> Name | None:
    match ref:
        case SApplication(SVar(p), SVar(b)) if p != binder and b == binder:
            return p
        case _:
            return None


def _merge_pred_sort(acc: dict[Name, SType], p: Name, sort: SType) -> None:
    if p in acc:
        if acc[p] != sort:
            raise ImplicitRefinementQuantError(
                f"refinement parameter {p} used with conflicting domain types {acc[p]} and {sort}"
            )
    else:
        acc[p] = sort


def _merge_dicts(dst: dict[Name, SType], src: dict[Name, SType]) -> None:
    for p, s in src.items():
        _merge_pred_sort(dst, p, s)


def collect_free_refinement_predicate_sorts(ty: SType, bound: frozenset[Name]) -> dict[Name, SType]:
    """Predicate names that appear as `p binder` in refinements and are not bound by an enclosing SRefinementPolymorphism."""

    def rec(ty: SType, bound: frozenset[Name]) -> dict[Name, SType]:
        return collect_free_refinement_predicate_sorts(ty, bound)

    out: dict[Name, SType] = {}
    match ty:
        case STypeVar(_):
            pass
        case STypeConstructor(_, args):
            for a in args:
                _merge_dicts(out, rec(a, bound))
        case SAbstractionType(_, vt, rt):
            _merge_dicts(out, rec(vt, bound))
            _merge_dicts(out, rec(rt, bound))
        case SRefinedType(bn, base, ref):
            _merge_dicts(out, rec(base, bound))
            p = _parametric_predicate_name(ref, bn)
            if p is not None and p not in bound:
                _merge_pred_sort(out, p, base)
        case STypePolymorphism(_, _, body):
            _merge_dicts(out, rec(body, bound))
        case SRefinementPolymorphism(n, s, body):
            nb = bound | {n}
            _merge_dicts(out, rec(s, bound))
            _merge_dicts(out, rec(body, nb))
        case _:
            raise AssertionError(f"collect_free_refinement_predicate_sorts: unknown {ty!r}")
    return out


def _wrap_free_predicate_sorts(ty: SType) -> SType:
    preds = collect_free_refinement_predicate_sorts(ty, frozenset())
    if not preds:
        return ty
    wrapped = ty
    for p in sorted(preds.keys(), key=lambda n: (n.name, n.id)):
        wrapped = SRefinementPolymorphism(p, preds[p], wrapped)
    return wrapped


def _transform(ty: SType) -> SType:
    def rec(ty: SType) -> SType:
        return _transform(ty)

    match ty:
        case STypePolymorphism(n, k, b, loc=loc):
            return STypePolymorphism(n, k, _wrap_free_predicate_sorts(rec(b)), loc=loc)
        case SAbstractionType(v, vt, rt, loc=loc):
            return SAbstractionType(v, rec(vt), rec(rt), loc=loc)
        case SRefinedType(bn, base, ref, loc=loc):
            return SRefinedType(bn, rec(base), ref, loc=loc)
        case SRefinementPolymorphism(n, s, b, loc=loc):
            return SRefinementPolymorphism(n, rec(s), rec(b), loc=loc)
        case STypeConstructor(nm, args, loc=loc):
            return STypeConstructor(nm, [rec(a) for a in args], loc=loc)
        case STypeVar(_):
            return ty
        case _:
            raise AssertionError(f"_transform: unknown {ty!r}")


def add_implicit_refinement_polymorphism(ty: SType) -> SType:
    """Close free refinement parameters with SRefinementPolymorphism, under each type forall and at the top level."""
    return _wrap_free_predicate_sorts(_transform(ty))
