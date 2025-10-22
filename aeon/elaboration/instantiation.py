from __future__ import annotations

from aeon.sugar.stypes import (
    SAbstractionType,
    SRefinedType,
    SType,
    STypeConstructor,
    STypePolymorphism,
    STypeVar,
)
from aeon.sugar.substitutions import normalize
from aeon.utils.name import Name


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
            return SAbstractionType(name, rec(vty), rec(rty), loc=loc)
        case STypePolymorphism(name, kind, body, loc):
            # TODO: Double-check alpha_renaming in substitution
            if name == alpha:
                return ty
            else:
                return STypePolymorphism(name, kind, rec(body), loc=loc)
        case STypeConstructor(name, args, loc):
            return STypeConstructor(name, [rec(a) for a in args], loc=loc)
        case _:
            return ty


# TODO: NOW! what is the difference in these two functions?
def type_variable_instantiation(ty: SType, alpha: str, beta: SType) -> SType:
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
            return SAbstractionType(var_name, rec(var_type), rec(ret_type), loc=loc)
        case STypePolymorphism(name, kind, body, loc):
            if name == alpha:
                return ty
            else:
                return STypePolymorphism(name, kind, rec(body), loc=loc)
        case STypeConstructor(name, args, loc):
            return STypeConstructor(name, [rec(a) for a in args], loc=loc)
        case _:
            assert False
