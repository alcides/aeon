from __future__ import annotations

from aeon.core.liquid import LiquidVar
from aeon.core.liquid_ops import mk_liquid_and
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import AbstractionType, RefinementPolymorphism, TypeConstructor
from aeon.core.types import RefinedType
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.utils.name import Name


def type_substitution(t: Type, alpha: Name, beta: Type) -> Type:
    """t[alpha := beta], standard substition."""
    assert isinstance(t, Type)

    def rec(x):
        return type_substitution(x, alpha, beta)

    match t:
        case TypeVar(name):
            if name == alpha:
                return beta
            else:
                return t
        case RefinedType(name, ity, ref, loc):
            match rec(ity):
                case RefinedType(iname, iity, iref) as city:
                    return RefinedType(
                        name, iity, mk_liquid_and(ref, substitution_in_liquid(iref, LiquidVar(name), iname)), loc=loc
                    )
                case AbstractionType(_, _, _):
                    assert False, f"Abstraction types cannot be refined: {t} to {ity} to {rec(ity)}"
                case city:
                    return RefinedType(name, city, ref, loc=loc)
        case AbstractionType(aname, aty, rty, loc):
            return AbstractionType(aname, rec(aty), rec(rty), loc=loc)
        case TypePolymorphism(name, kind, body, loc):
            if name == alpha:
                return t
            else:
                return TypePolymorphism(name, kind, rec(body), loc=loc)
        case RefinementPolymorphism(rname, sort, body, loc):
            return RefinementPolymorphism(rname, rec(sort), rec(body), loc=loc)
        case TypeConstructor(name, args, loc):
            return TypeConstructor(name, [rec(arg) for arg in args], loc=loc)
        case _:
            assert False, f"Not considered: {t} ({type(t)})"


def type_variable_instantiation(t: Type, alpha: Name, beta: Type) -> Type:
    """t[alpha |-> beta], instantiation."""

    def rec(x):
        return type_variable_instantiation(x, alpha, beta)

    match t:
        case TypeConstructor():
            return t
        case TypeVar(name) if name == alpha:
            return beta
        case TypeVar():
            return t
        case RefinedType(tname, TypeVar(name=tvn), tref, tloc) if tvn == alpha:
            match beta:
                case RefinedType(bname, btype, bref, _):
                    return RefinedType(
                        tname,
                        btype,
                        mk_liquid_and(
                            tref,
                            substitution_in_liquid(bref, LiquidVar(tname), bname),
                        ),
                        tloc,
                    )
                case _:
                    return RefinedType(tname, rec(t.type), tref, tloc)
        case RefinedType(name, inner, ref, loc):
            return RefinedType(name, rec(inner), ref, loc)
        case AbstractionType(vn, vt, rt, loc):
            return AbstractionType(vn, rec(vt), rec(rt), loc)
        case TypePolymorphism(name, kind, body, loc):
            return TypePolymorphism(name, kind, rec(body), loc)
        case RefinementPolymorphism(name, sort, body, loc):
            return RefinementPolymorphism(name, rec(sort), rec(body), loc)
        case _:
            assert False
