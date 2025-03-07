from __future__ import annotations

from aeon.core.liquid import LiquidVar
from aeon.core.liquid_ops import mk_liquid_and
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import AbstractionType, TypeConstructor
from aeon.core.types import BaseType
from aeon.core.types import RefinedType
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar


def type_substitution(t: Type, alpha: str, beta: Type) -> Type:
    """t[alpha := beta], standard substition."""
    assert isinstance(t, Type)

    def rec(x):
        return type_substitution(x, alpha, beta)

    match t:
        case BaseType(_):
            return t
        case TypeVar(name):
            if name == alpha:
                return beta
            else:
                return t
        case RefinedType(name, ity, ref):
            return RefinedType(name, rec(ity), ref)
        case AbstractionType(aname, aty, rty):
            return AbstractionType(aname, rec(aty), rec(rty))
        case TypePolymorphism(name, kind, body):
            if name == alpha:
                return t
            else:
                return TypePolymorphism(name, kind, rec(body))
        case TypeConstructor(name, args):
            return TypeConstructor(name, [rec(arg) for arg in args])
        case _:
            assert False, f"Not considered: {t} ({type(t)})"


def type_variable_instantiation(t: Type, alpha: str, beta: Type) -> Type:
    """t[alpha |-> beta], instantiation."""

    def rec(x):
        return type_variable_instantiation(x, alpha, beta)

    if isinstance(t, BaseType):
        return t
    elif isinstance(t, TypeVar) and t.name == alpha:
        return beta
    elif isinstance(t, TypeVar) and t.name != alpha:
        return t
    elif (isinstance(t, RefinedType) and isinstance(t.type, TypeVar)
          and t.type.name == alpha and isinstance(beta, RefinedType)):
        return RefinedType(
            t.name,
            beta.type,
            mk_liquid_and(
                t.refinement,
                substitution_in_liquid(beta.refinement, LiquidVar(t.name),
                                       beta.name),
            ),
        )
    elif isinstance(t, RefinedType):
        return RefinedType(t.name, rec(t.type), t.refinement)
    elif isinstance(t, AbstractionType):
        return AbstractionType(t.var_name, rec(t.var_type), rec(t.type))
    elif isinstance(t, TypePolymorphism):  # Todo: alpha renaming?
        target = t
        while target.name == alpha:
            new_name = target.name + "_fresh_"
            target = TypePolymorphism(
                new_name,
                t.kind,
                type_substitution(t.body, alpha, TypeVar(new_name)),
            )
        return TypePolymorphism(target.name, target.kind, rec(target.body))
    else:
        assert False
