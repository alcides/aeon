from __future__ import annotations

from aeon.core.liquid import LiquidVar
from aeon.core.liquid_ops import mk_liquid_and
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import AbstractionType
from aeon.core.types import BaseType
from aeon.core.types import RefinedType
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar


def type_substition(t: Type, alpha: str, beta: Type) -> Type:
    """t[alpha := beta], standard substition."""

    rec = lambda x: type_substition(x, alpha, beta)

    if isinstance(t, BaseType):
        return t
    elif isinstance(t, TypeVar) and t.name == alpha:
        return beta
    elif isinstance(t, TypeVar) and t.name != alpha:
        return t
    elif isinstance(t, RefinedType):
        return RefinedType(t.name, rec(t.type), t.refinement)
    elif isinstance(t, AbstractionType):
        return AbstractionType(t.var_name, rec(t.var_type), rec(t.type))
    elif isinstance(t, TypePolymorphism):
        target = t
        while target.name == alpha:
            new_name = target.name + "_fresh_"
            target = TypePolymorphism(
                new_name,
                t.kind,
                type_substition(t.body, alpha, TypeVar(new_name)),
            )
        return AbstractionType(target.var_name, target.var_type,
                               rec(target.type))
    else:
        assert False


def type_variable_instantiation(t: Type, alpha: str, beta: Type) -> Type:
    """t[alpha |-> beta], instantiation."""

    rec = lambda x: type_variable_instantiation(x, alpha, beta)

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
                substitution_in_liquid(beta.type, LiquidVar(t.name),
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
                type_substition(t.body, alpha, TypeVar(new_name)),
            )
        return AbstractionType(target.var_name, target.var_type,
                               rec(target.type))
    else:
        assert False
