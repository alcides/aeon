from __future__ import annotations

from abc import ABC
from dataclasses import dataclass

from aeon.core.liquid import LiquidLiteralFloat, LiquidLiteralInt, LiquidLiteralString, liquid_free_vars
from aeon.core.liquid import LiquidHole
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidTerm
from aeon.utils.name import Name


class Kind(ABC):

    def __repr__(self):
        return str(self)


class BaseKind(Kind):

    def __eq__(self, o):
        return self.__class__ == o.__class__

    def __str__(self):
        return "Β"

    def __hash__(self):
        return super().__hash__()


class StarKind(Kind):

    def __eq__(self, o):
        return self.__class__ == o.__class__

    def __str__(self):
        return "★"

    def __hash__(self):
        return super().__hash__()


class Type(ABC):
    pass


@dataclass
class BaseType(Type):
    name: Name

    def __repr__(self):
        return f"{self.name}"

    def __eq__(self, other):
        return isinstance(other, BaseType) and other.name == self.name

    def __hash__(self) -> int:
        return hash(self.name)


@dataclass
class TypeVar(Type):
    name: Name

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


t_unit = BaseType(Name("Unit", 2))
t_bool = BaseType(Name("Bool", 3))
t_int = BaseType(Name("Int", 4))
t_float = BaseType(Name("Float", 5))
t_string = BaseType(Name("String", 6))

builtin_core_types = [t_unit, t_bool, t_int, t_float, t_string]

top = Top()


@dataclass
class AbstractionType(Type):
    var_name: Name
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
    name: Name
    type: BaseType | TypeVar | TypeConstructor
    refinement: LiquidTerm

    def __repr__(self):
        return f"{{ {self.name}:{self.type} | {self.refinement} }}"

    def __eq__(self, other):
        return (
            isinstance(other, RefinedType)
            and self.name == other.name
            and self.type == other.type
            and self.refinement == other.refinement
        )

    def __hash__(self) -> int:
        return hash(self.name) + hash(self.type) + hash(self.refinement)


@dataclass
class TypePolymorphism(Type):
    name: Name  # alpha
    kind: Kind
    body: Type

    def __str__(self):
        return f"forall {self.name}:{self.kind}, {self.body}"

    def __hash__(self) -> int:
        return hash(self.name) + hash(self.kind) + hash(self.body)


@dataclass
class TypeConstructor(Type):
    name: Name
    args: list[Type]

    def __str__(self):
        args = ", ".join(str(a) for a in self.args)
        return f"{self.name} {args}"


# This class is here to prevent circular imports.


@dataclass
class LiquidHornApplication(LiquidTerm):
    name: Name
    argtypes: list[tuple[LiquidTerm, BaseType | TypeVar | TypeConstructor]]

    def __post_init__(self):
        assert isinstance(self.name, str)
        for term, ty in self.argtypes:
            match term:
                case LiquidLiteralBool(_):
                    assert ty == BaseType("Bool")
                case LiquidLiteralInt(_):
                    assert ty == BaseType("Int")
                case LiquidLiteralFloat(_):
                    assert ty == BaseType("Float")
                case LiquidLiteralString(_):
                    assert ty == BaseType("String")

    def __repr__(self):
        j = ", ".join([f"{n}:{t}" for (n, t) in self.argtypes])
        return f"?{self.name}({j})"

    def __eq__(self, other):
        return isinstance(other, LiquidHornApplication) and other.name == self.name

    def __hash__(self) -> int:
        return hash(self.name)


def extract_parts(t: Type) -> tuple[Name, BaseType | TypeVar | TypeConstructor, LiquidTerm]:
    assert (
        isinstance(t, BaseType)
        or isinstance(t, RefinedType)
        or isinstance(
            t,
            TypeVar,
        )
        or isinstance(t, TypeConstructor)
    )
    if isinstance(t, TypeVar):
        return (Name("_"), t_int, LiquidLiteralBool(True))
    elif isinstance(t, RefinedType):
        return (t.name, t.type, t.refinement)
    else:
        return (
            Name("_"),
            t,
            LiquidLiteralBool(True),
        )  # None could be a fresh name from context


def is_bare(t: Type) -> bool:
    """Returns whether the type is bare."""
    match t:
        case BaseType(_) | Top() | TypeVar():
            return True
        case RefinedType(_, _, ref):
            return ref == LiquidHole() or isinstance(ref, LiquidHornApplication)
        case AbstractionType(_, _, vtype):
            return is_bare(vtype) and is_bare(vtype)
        case TypePolymorphism(_, _, ty):
            return is_bare(ty)
        case TypeConstructor(_, _):
            return True
        case _:
            assert False, f"Unknown type {t} ({type(t)})"


def base(ty: Type) -> Type:
    """Returns the base type of a Refined Type"""
    if isinstance(ty, RefinedType):
        return ty.type
    return ty


def type_free_term_vars(t: Type) -> list[Name]:
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
        assert False, f"Unable to extract {t} ({type(t)})"


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
