from typing import List, Tuple, Union
from aeon.core.liquid import LiquidLiteralBool, LiquidTerm, liquid_free_vars


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

    def __hash__(self) -> int:
        return hash(self.name)


class TypeVar(Type):
    name: str

    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return u"{}".format(self.name)

    def __eq__(self, other):
        return isinstance(other, BaseType) and other.name == self.name

    def __hash__(self) -> int:
        return hash(self.name)


class Top(Type):
    def __repr__(self):
        return u"⊤"

    def __eq__(self, other):
        return isinstance(other, Top)

    def __str__(self):
        return repr(self)

    def __hash__(self) -> int:
        return hash("Top")


class Bottom(Type):
    def __repr__(self):
        return u"⊥"

    def __eq__(self, other):
        return isinstance(other, Bottom)

    def __str__(self):
        return repr(self)

    def __hash__(self) -> int:
        return hash("Bottom")


t_bool = BaseType("Bool")
t_int = BaseType("Int")
t_float = BaseType("Float")
t_string = BaseType("String")

top = Top()
bottom = Bottom()


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
        return (
            isinstance(other, AbstractionType)
            and self.var_name == other.var_name
            and self.var_type == other.var_type
            and self.type == other.type
        )

    def __hash__(self) -> int:
        return hash(self.var_name) + hash(self.var_type) + hash(self.type)


class RefinedType(Type):
    name: str
    type: Union[BaseType, TypeVar]
    refinement: LiquidTerm

    def __init__(self, name: str, ty: Union[BaseType, TypeVar], refinement: LiquidTerm):
        self.name = name
        self.type = ty
        self.refinement = refinement

    def __repr__(self):
        return u"{{ {}:{} | {} }}".format(self.name, self.type, self.refinement)

    def __eq__(self, other):
        return (
            isinstance(other, RefinedType)
            and self.name == other.name
            and self.type == other.type
            and self.refinement == other.refinement
        )

    def __hash__(self) -> int:
        return hash(self.name) + hash(self.type) + hash(self.refinement)


def extract_parts(
    t: Union[RefinedType, BaseType, TypeVar]
) -> Tuple[str, Union[BaseType, TypeVar], LiquidTerm]:
    if isinstance(t, RefinedType):
        return (t.name, t.type, t.refinement)
    else:
        return (
            "_",
            t,
            LiquidLiteralBool(True),
        )  # None could be a fresh name from context


def base(ty: Type) -> Type:
    if isinstance(ty, RefinedType):
        return ty.type
    return ty


def type_free_term_vars(t: Type) -> List[str]:
    if isinstance(t, BaseType):
        return []
    elif isinstance(t, TypeVar):
        return []
    elif isinstance(t, AbstractionType):
        afv = type_free_term_vars(t.var_type)
        rfv = type_free_term_vars(t.type)
        return [x for x in afv + rfv if x != t.var_name]
    elif isinstance(t, RefinedType):
        ifv = type_free_term_vars(t.type)
        rfv = liquid_free_vars(t.refinement)
        return [x for x in ifv + rfv if x != t.name]
    return []


def args_size_of_type(t: Type) -> int:
    if isinstance(t, BaseType):
        return 0
    elif isinstance(t, TypeVar):
        return 0
    elif isinstance(t, RefinedType):
        return 0
    elif isinstance(t, AbstractionType):
        return 1 + args_size_of_type(t.type)
    else:
        assert False
