from __future__ import annotations

from aeon.sugar.stypes import (
    SAbstractionType,
    SRefinedType,
    SRefinementPolymorphism,
    SType,
    STypeConstructor,
    STypePolymorphism,
    STypeVar,
    get_type_vars,
)
from aeon.sugar.substitutions import normalize
from aeon.utils.name import Name, fresh_counter


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
            return SAbstractionType(name, rec(vty), rec(rty), loc=loc, multiplicity=ty.multiplicity)
        case STypePolymorphism(name, kind, body, loc):
            if name == alpha:
                # The binder shadows alpha: nothing free to substitute below.
                return ty
            if name in (tv.name for tv in get_type_vars(beta)):
                # The binder would capture a free type variable of beta;
                # alpha-rename it to a fresh name first.
                fresh = Name(name.name, fresh_counter.fresh())
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
            return SAbstractionType(var_name, rec(var_type), rec(ret_type), loc=loc, multiplicity=ty.multiplicity)
        case STypePolymorphism(name, kind, body, loc):
            if name == alpha:
                return ty
            if name in (tv.name for tv in get_type_vars(beta)):
                fresh = Name(name.name, fresh_counter.fresh())
                body = type_variable_instantiation(body, name, STypeVar(fresh))
                name = fresh
            return STypePolymorphism(name, kind, rec(body), loc=loc)
        case SRefinementPolymorphism(name, sort, body, loc):
            return SRefinementPolymorphism(name, rec(sort), rec(body), loc=loc)
        case STypeConstructor(name, args, loc):
            return STypeConstructor(name, [rec(a) for a in args], loc=loc)
        case _:
            assert False
