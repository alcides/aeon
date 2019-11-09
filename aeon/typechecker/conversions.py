from typing import cast

from ..types import TypingContext, Type, BasicType, RefinedType, TypeApplication, TypeAbstraction

from .substitutions import substitution_type_in_type


class NoTypeConvertionRule(Exception):
    pass


def c_base(t: BasicType):
    return t


# TODO: paper
def c_beta(t: TypeApplication):
    tabs = type_conversion(t.target)
    U = type_conversion(t.argument)
    if isinstance(t.target, TypeAbstraction):
        tn = t.target.name
        T = t.target.type
        return substitution_type_in_type(T, U, tn)
    return t


def c_tabs(t: TypeAbstraction):
    ntype = type_conversion(t.type)
    return TypeAbstraction(t.name, t.kind, ntype)


def c_twhere(t: RefinedType):
    ntype = type_conversion(t.type)
    return RefinedType(t.name, ntype, t.cond)


def c_tapp(t: TypeApplication):
    Tp = type_conversion(t.target)
    Up = type_conversion(t.argument)
    return TypeApplication(Tp, Up)


def type_conversion(t: Type):
    """ T ⇩ U  """
    if isinstance(t, BasicType):
        return c_base(t)
    elif isinstance(t, TypeApplication) and isinstance(t.target,
                                                       TypeAbstraction):
        return c_beta(t)
    elif isinstance(t, TypeApplication):
        return c_beta(c_tapp(t))
    elif isinstance(t, TypeAbstraction):
        return c_tabs(t)
    elif isinstance(t, RefinedType):
        return c_twhere(t)
    return t
