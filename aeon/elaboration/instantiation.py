from __future__ import annotations

from aeon.sugar.stypes import (
    SAbstractionType,
    SRefinedType,
    SRefinementPolymorphism,
    SType,
    STypeConstructor,
    STypePolymorphism,
    STypeVar,
)
from aeon.sugar.substitutions import normalize
from aeon.utils.name import Name, fresh_counter


def free_type_var_names(ty: SType, *, include_bound: bool = False) -> set[Name]:
    """Best-effort set of free type-variable names of ``ty``.

    Unlike ``aeon.sugar.stypes.get_type_vars`` this never raises on
    elaboration-internal ``SType`` nodes (``UnificationVar``/``Union``/
    ``Intersection``, see ``aeon.elaboration``): those are not part of the
    surface ``SType`` grammar, so they are handled generically by recursing
    into any ``SType``-valued attributes they carry.

    ``include_bound`` also collects polymorphic binders, for choosing a new
    binder that cannot collide with names supplied through low-level APIs.
    """

    def rec(child: SType) -> set[Name]:
        return free_type_var_names(child, include_bound=include_bound)

    match ty:
        case STypeVar(name):
            return {name}
        case SRefinedType(_, ity, _):
            return rec(ity)
        case SAbstractionType(_, vty, rty):
            return rec(vty) | rec(rty)
        case STypePolymorphism(name, _, body):
            return rec(body) | {name} if include_bound else rec(body) - {name}
        case SRefinementPolymorphism(_, sort, body):
            return rec(sort) | rec(body)
        case STypeConstructor(_, args):
            return set().union(*(rec(a) for a in args)) if args else set()
        case _:
            # Elaboration-internal variants (UnificationVar.lower/upper,
            # Union.united, Intersection.intersected) and any future node:
            # recurse into SType-valued children without importing them.
            acc: set[Name] = set()
            for attr in ("lower", "upper", "united", "intersected"):
                for child in getattr(ty, attr, ()) or ():
                    if isinstance(child, SType):
                        acc |= rec(child)
            return acc


def _fresh_type_binder(name: Name, alpha: Name, body: SType, replacement: SType) -> Name:
    forbidden = (
        {name, alpha}
        | free_type_var_names(body, include_bound=True)
        | free_type_var_names(replacement, include_bound=True)
    )
    fresh = Name(name.name, fresh_counter.fresh())
    while fresh in forbidden:
        fresh = Name(name.name, fresh_counter.fresh())
    return fresh


def type_substitution(ty: SType, alpha: Name, beta: SType) -> SType:
    """t[alpha := beta], standard substition."""

    def rec(x):
        return type_substitution(x, alpha, beta)

    ty = normalize(ty)

    match ty:
        case STypeVar(name):
            if name == alpha:
                return beta
            else:
                return ty
        case SRefinedType(name, ity, ref, loc):
            return normalize(SRefinedType(name, rec(ity), ref, loc=loc))
        case SAbstractionType(name, vty, rty, loc):
            return SAbstractionType(
                name, rec(vty), rec(rty), loc=loc, multiplicity=ty.multiplicity, is_instance=ty.is_instance
            )
        case STypePolymorphism(name, kind, body, loc):
            if name == alpha:
                # The binder shadows alpha: nothing free to substitute below.
                return ty
            if name in free_type_var_names(beta):
                # The binder would capture a free type variable of beta;
                # alpha-rename it to a fresh name first.
                fresh = _fresh_type_binder(name, alpha, body, beta)
                body = type_substitution(body, name, STypeVar(fresh))
                name = fresh
            return STypePolymorphism(name, kind, rec(body), loc=loc)
        case SRefinementPolymorphism(name, sort, body, loc):
            return SRefinementPolymorphism(name, rec(sort), rec(body), loc=loc)
        case STypeConstructor(name, args, loc):
            return STypeConstructor(name, [rec(a) for a in args], loc=loc)
        case _:
            return ty


def type_variable_instantiation(ty: SType, alpha: Name, beta: SType) -> SType:
    """t[alpha |-> beta], instantiation."""

    ty = normalize(ty)

    def rec(x: SType):
        return type_variable_instantiation(x, alpha, beta)

    match ty:
        case STypeVar(name):
            if name == alpha:
                return beta
            else:
                return ty
        case SRefinedType(name, ity, ref, loc):
            return normalize(SRefinedType(name, rec(ity), ref, loc=loc))
        case SAbstractionType(var_name, var_type, ret_type, loc):
            return SAbstractionType(
                var_name,
                rec(var_type),
                rec(ret_type),
                loc=loc,
                multiplicity=ty.multiplicity,
                is_instance=ty.is_instance,
            )
        case STypePolymorphism(name, kind, body, loc):
            if name == alpha:
                return ty
            if name in free_type_var_names(beta):
                fresh = _fresh_type_binder(name, alpha, body, beta)
                body = type_variable_instantiation(body, name, STypeVar(fresh))
                name = fresh
            return STypePolymorphism(name, kind, rec(body), loc=loc)
        case SRefinementPolymorphism(name, sort, body, loc):
            return SRefinementPolymorphism(name, rec(sort), rec(body), loc=loc)
        case STypeConstructor(name, args, loc):
            return STypeConstructor(name, [rec(a) for a in args], loc=loc)
        case _:
            assert False
