from __future__ import annotations

from aeon.sugar.stypes import SAbstractionType, SBaseType, SRefinedType, SType, STypePolymorphism, STypeVar
from aeon.sugar.substitutions import normalize


def type_substitution(ty: SType, alpha: str, beta: SType) -> SType:
    """t[alpha := beta], standard substition."""

    def rec(x):
        return type_substitution(x, alpha, beta)

    ty = normalize(ty)

    match ty:
        case SBaseType(_):
            return ty
        case STypeVar(name):
            if name == alpha:
                return beta
            else:
                return ty
        case SRefinedType(name, ity, ref):
            return normalize(SRefinedType(name, rec(ity), ref))
        case SAbstractionType(name, vty, rty):
            return SAbstractionType(name, rec(vty), rec(rty))
        case STypePolymorphism(name, kind, body):
            # TODO: Double-check alpha_renaming in substitution
            if name == alpha:
                return ty
            else:
                return STypePolymorphism(name, kind, rec(body))
        case _:
            assert False


# TODO: NOW! what is the difference in these two functions?
def type_variable_instantiation(ty: SType, alpha: str, beta: SType) -> SType:
    """t[alpha |-> beta], instantiation."""

    ty = normalize(ty)

    def rec(x: SType):
        return type_variable_instantiation(x, alpha, beta)

    match ty:
        case SBaseType(_):
            return ty
        case STypeVar(name):
            if name == alpha:
                return beta
            else:
                return ty
        case SRefinedType(name, ity, ref):
            return normalize(SRefinedType(name, rec(ity), ref))
        case SAbstractionType(var_name, var_type, ret_type):
            return SAbstractionType(var_name, rec(var_type), rec(ret_type))
        case STypePolymorphism(name, kind, body):
            if name == alpha:
                return ty
            else:
                return STypePolymorphism(name, kind, rec(body))
        case _:
            assert False
