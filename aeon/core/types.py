from __future__ import annotations

from abc import ABC
from dataclasses import dataclass, field

from aeon.core.liquid import LiquidLiteralFloat, LiquidLiteralInt, LiquidLiteralString, liquid_free_vars
from aeon.core.liquid import LiquidHole
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidTerm
from aeon.utils.location import Location
from aeon.utils.name import fresh_counter, Name


# TODO: convert to ENUM
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
    loc: Location


@dataclass
class TypeVar(Type):
    name: Name

    def __post_init__(self):
        if self.name.name in ["Int", "Bool"]:
            assert False

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
    type: TypeConstructor | TypeVar | TypeConstructor
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
    args: list[Type] = field(default_factory=list)

    def __str__(self):
        args = ", ".join(str(a) for a in self.args)
        return f"{self.name} {args}"

    def __eq__(self, other):
        return isinstance(other, TypeConstructor) and other.name == self.name and self.args == other.args

    def __hash__(self) -> int:
        return hash(self.name) + sum(hash(a) for a in self.args)


# Default type constructors


t_unit = TypeConstructor(Name("Unit", 0), [])
t_bool = TypeConstructor(Name("Bool", 0), [])
t_int = TypeConstructor(Name("Int", 0), [])
t_float = TypeConstructor(Name("Float", 0), [])
t_string = TypeConstructor(Name("String", 0), [])

builtin_core_types = [t_unit, t_bool, t_int, t_float, t_string]

top = Top()


# This class is here to prevent circular imports.


@dataclass
class LiquidHornApplication(LiquidTerm):
    name: Name
    argtypes: list[tuple[LiquidTerm, TypeConstructor | TypeVar | TypeConstructor]]

    def __post_init__(self):
        assert isinstance(self.name, Name)
        for term, ty in self.argtypes:
            match term:
                case LiquidLiteralBool(_):
                    assert ty == TypeConstructor(Name("Bool", 0))
                case LiquidLiteralInt(_):
                    assert ty == TypeConstructor(Name("Int", 0))
                case LiquidLiteralFloat(_):
                    assert ty == TypeConstructor(Name("Float", 0))
                case LiquidLiteralString(_):
                    assert ty == TypeConstructor(Name("String", 0))

    def __repr__(self):
        j = ", ".join([f"{n}:{t}" for (n, t) in self.argtypes])
        return f"?{self.name}({j})"

    def __eq__(self, other):
        return isinstance(other, LiquidHornApplication) and other.name == self.name

    def __hash__(self) -> int:
        return hash(self.name)


liq_true = LiquidLiteralBool(True)


def extract_parts(t: Type) -> tuple[Name, TypeConstructor | TypeVar | TypeConstructor, LiquidTerm]:
    assert (
        isinstance(t, TypeConstructor)
        or isinstance(t, RefinedType)
        or isinstance(
            t,
            TypeVar,
        )
        or isinstance(t, TypeConstructor)
    )
    match t:
        case RefinedType(name, ity, ref):
            return (name, ity, ref)
        case _:
            return (Name("_", fresh_counter.fresh()), t, liq_true)


def is_bare(t: Type) -> bool:
    """Returns whether the type is bare."""
    match t:
        case TypeConstructor(_, _) | Top() | TypeVar():
            return True
        case RefinedType(_, _, ref):
            return ref == LiquidHole() or isinstance(ref, LiquidHornApplication)
        case AbstractionType(_, _, vtype):
            return is_bare(vtype) and is_bare(vtype)
        case TypePolymorphism(_, _, ty):
            return is_bare(ty)
        case _:
            assert False, f"Unknown type {t} ({type(t)})"


def base(ty: Type) -> Type:
    """Returns the base type of a Refined Type"""
    if isinstance(ty, RefinedType):
        return ty.type
    return ty


def type_free_term_vars(t: Type) -> list[Name]:
    from aeon.prelude.prelude import ALL_OPS

    if isinstance(t, TypeConstructor):
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
    if isinstance(t, TypeConstructor):
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
