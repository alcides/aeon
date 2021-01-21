from typing import Tuple
from aeon.core.liquid import LiquidLiteralBool, LiquidTerm


class Type(object):
    pass


class BaseType(Type):
    name: str

    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return u"{}".format(self.name)

    def __eq__(self, other):
        return isinstance(other, BaseType) and other.name == self.name


t_bool = BaseType("Bool")
t_int = BaseType("Int")
t_float = BaseType("Float")
t_string = BaseType("String")


class AbstractionType(Type):
    var_name: str
    var_type: Type
    type: Type

    def __init__(self, var_name: str, var_type: Type, type: Type):
        self.var_name = var_name
        self.var_type = var_type
        self.type = type

    def __repr__(self):
        return u"({}:{}) -> {}".format(self.var_name, self.var_type, self.type)

    def __eq__(self, other):
        return isinstance(other, AbstractionType) and \
            self.var_name == other.var_name and \
            self.var_type == other.var_type and \
            self.type == other.type


class RefinedType(Type):
    name: str
    type: BaseType
    refinement: LiquidTerm

    def __init__(self, name: str, type: BaseType, refinement: LiquidTerm):
        self.name = name
        self.type = type
        self.refinement = refinement

    def __repr__(self):
        return u"{{ {}:{} | {} }}".format(self.name, self.type,
                                          self.refinement)

    def __eq__(self, other):
        return isinstance(other, RefinedType) and \
            self.name == other.name and \
            self.type == other.type and \
            self.refinement == other.refinement


def extract_parts(t: Type) -> Tuple[str, BaseType, LiquidTerm]:
    if isinstance(t, RefinedType):
        return (t.name, t.type, t.refinement)
    else:
        return ("_", t, LiquidLiteralBool(True)
                )  # None could be a fresh name from context
