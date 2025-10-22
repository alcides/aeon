from __future__ import annotations

from aeon.core.liquid import LiquidVar
from aeon.core.liquid_ops import mk_liquid_and
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import AbstractionType, TypeConstructor
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
        case TypeConstructor(name, args, loc):
            return TypeConstructor(name, [rec(arg) for arg in args], loc=loc)
        case _:
            assert False, f"Not considered: {t} ({type(t)})"


def type_variable_instantiation(t: Type, alpha: Name, beta: Type) -> Type:
    """t[alpha |-> beta], instantiation."""

    def rec(x):
        return type_variable_instantiation(x, alpha, beta)

    if isinstance(t, TypeConstructor):
        return t
    elif isinstance(t, TypeVar) and t.name == alpha:
        return beta
    elif isinstance(t, TypeVar) and t.name != alpha:
        return t
    elif (
        isinstance(t, RefinedType)
        and isinstance(t.type, TypeVar)
        and t.type.name == alpha
        and isinstance(beta, RefinedType)
    ):
        return RefinedType(
            t.name,
            beta.type,
            mk_liquid_and(
                t.refinement,
                substitution_in_liquid(beta.refinement, LiquidVar(t.name), beta.name),
            ),
            t.loc,
        )
    elif isinstance(t, RefinedType):
        return RefinedType(t.name, rec(t.type), t.refinement, t.loc)
    elif isinstance(t, AbstractionType):
        return AbstractionType(t.var_name, rec(t.var_type), rec(t.type), t.loc)
    elif isinstance(t, TypePolymorphism):
        return TypePolymorphism(t.name, t.kind, rec(t.body), t.loc)
    else:
        assert False
