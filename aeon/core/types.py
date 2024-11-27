from __future__ import annotations

from abc import ABC
from dataclasses import dataclass

from aeon.core.liquid import LiquidHornApplication, liquid_free_vars
from aeon.core.liquid import LiquidHole
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidTerm


class Kind(ABC):

    def __repr__(self):
        return str(self)


class BaseKind(Kind):

    def __eq__(self, o):
        return self.__class__ == o.__class__

    def __str__(self):
        return "Β"


class StarKind(Kind):

    def __eq__(self, o):
        return self.__class__ == o.__class__

    def __str__(self):
        return "★"


class Type(ABC):
    pass


@dataclass
class BaseType(Type):
    name: str

    def __repr__(self):
        return f"{self.name}"

    def __eq__(self, other):
        return isinstance(other, BaseType) and other.name == self.name

    def __hash__(self) -> int:
        return hash(self.name)


@dataclass
class TypeVar(Type):
    name: str

    def __repr__(self):
        return f"{self.name}"

    def __eq__(self, other):
        return isinstance(other, TypeVar) and other.name == self.name

    def __hash__(self) -> int:
        return hash(self.name)


class Top(Type):

    def __repr__(self):
        return "⊤"

    def __eq__(self, other):
        return isinstance(other, Top)

    def __str__(self):
        return repr(self)

    def __hash__(self) -> int:
        return hash("Top")


class Bottom(Type):

    def __repr__(self):
        return "⊥"

    def __eq__(self, other):
        return isinstance(other, Bottom)

    def __str__(self):
        return repr(self)

    def __hash__(self) -> int:
        return hash("Bottom")


t_unit = BaseType("Unit")
t_bool = BaseType("Bool")
t_int = BaseType("Int")
t_float = BaseType("Float")
t_string = BaseType("String")

top = Top()
bottom = Bottom()


@dataclass
class AbstractionType(Type):
    var_name: str
    var_type: Type
    type: Type

    def __repr__(self):
        return f"({self.var_name}:{self.var_type}) -> {self.type}"

    def __eq__(self, other):
        return (
            isinstance(other, AbstractionType)
            and self.var_name == other.var_name
            and self.var_type == other.var_type
            and self.type == other.type
        )

    def __hash__(self) -> int:
        return hash(self.var_name) + hash(self.var_type) + hash(self.type)


@dataclass
class RefinedType(Type):
    name: str
    type: BaseType | TypeVar
    refinement: LiquidTerm

    def __repr__(self):
        return f"{{ {self.name}:{self.type} | {self.refinement} }}"

    def __eq__(self, other):
        return (
            isinstance(other, RefinedType) and self.name == other.name
            and self.type == other.type
            and self.refinement == other.refinement
        )

    def __hash__(self) -> int:
        return hash(self.name) + hash(self.type) + hash(self.refinement)


@dataclass
class TypePolymorphism(Type):
    name: str  # alpha
    kind: Kind
    body: Type

    def __str__(self):
        return f"forall {self.name}:{self.kind}, {self.body}"


def extract_parts(t: Type) -> tuple[str, BaseType | TypeVar, LiquidTerm]:
    assert isinstance(t, BaseType) or isinstance(t, RefinedType) or isinstance(
        t,
        TypeVar,
    )
    if isinstance(t, TypeVar):
        return ("_", t_int, LiquidLiteralBool(True))
    elif isinstance(t, RefinedType):
        return (t.name, t.type, t.refinement)
    else:
        return (
            "_",
            t,
            LiquidLiteralBool(True),
        )  # None could be a fresh name from context


def is_bare(t: Type) -> bool:
    """Returns whether the type is bare."""
    if isinstance(t, BaseType):
        return True
    elif isinstance(t, Top):
        return True
    elif isinstance(t, Bottom):
        return True
    elif isinstance(t, RefinedType):
        return t.refinement == LiquidHole() or isinstance(
            t.refinement,
            LiquidHornApplication,
        )
    elif isinstance(t, AbstractionType):
        return is_bare(t.var_type) and is_bare(t.type)
    elif isinstance(t, TypePolymorphism):
        return is_bare(t.body)
    else:
        return False


def base(ty: Type) -> Type:
    """Returns the base type of a Refined Type"""
    if isinstance(ty, RefinedType):
        return ty.type
    return ty


def type_free_term_vars(t: Type) -> list[str]:
    from aeon.prelude.prelude import ALL_OPS

    if isinstance(t, BaseType):
        return []
    elif isinstance(t, TypeVar):
        return []
    elif isinstance(t, AbstractionType):
        afv = type_free_term_vars(t.var_type)
        rfv = type_free_term_vars(t.type)
        return [x for x in afv + rfv if x != t.var_name and x not in ALL_OPS]
    elif isinstance(t, RefinedType):
        ifv = type_free_term_vars(t.type)
        rfv = liquid_free_vars(t.refinement)
        return [x for x in ifv + rfv if x != t.name]
    elif isinstance(t, TypePolymorphism):
        return type_free_term_vars(t.body)
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
    elif isinstance(t, TypePolymorphism):
        return args_size_of_type(t.body)
    else:
        assert False


def get_type_vars(t: Type) -> set[TypeVar]:
    if isinstance(t, BaseType):
        return set()
    elif isinstance(t, TypeVar):
        return {t}
    elif isinstance(t, AbstractionType):
        return get_type_vars(t.var_type).union(get_type_vars(t.type))
    elif isinstance(t, RefinedType):
        return get_type_vars(t.type)
    elif isinstance(t, TypePolymorphism):
        return {t1 for t1 in get_type_vars(t.body) if t1.name != t.name}
    else:
        assert False


def refined_to_unrefined_type(ty: Type) -> Type:
    if isinstance(ty, RefinedType):
        return ty.type
    if isinstance(ty, AbstractionType):
        return AbstractionType(
            ty.var_name,
            refined_to_unrefined_type(ty.var_type),
            refined_to_unrefined_type(ty.type),
        )
    return ty


def extract_typelevel_freevars(ty: Type) -> list[str]:
    return [v.name for v in get_type_vars(ty)]
