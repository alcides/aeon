from __future__ import annotations

from abc import ABC
from dataclasses import dataclass, field

from aeon.core.types import (
    AbstractionType,
    BaseKind,
    BaseType,
    RefinedType,
    Top,
    TypeConstructor,
    TypePolymorphism,
    TypeVar,
)
from aeon.core.types import Kind
from aeon.core.types import StarKind
from aeon.core.types import Type
from aeon.utils.name import Name


class TypingContextEntry(ABC):
    pass

@dataclass
class VariableBinder(TypingContextEntry):
    name: Name
    type: Type

@dataclass
class UninterpretedBinder(TypingContextEntry):
    name: Name
    type: AbstractionType

@dataclass
class TypeBinder(TypingContextEntry):
    type_name: Name
    type_kind: Kind = field(default_factory=StarKind)


@dataclass
class TypeConstructorBinder(TypingContextEntry):
    name: Name
    args: list[Name]

@dataclass
class TypingContext:

    entries:list[TypingContextEntry]

    def with_var(self, name: Name, type: Type) -> TypingContext:
        return TypingContext(self.entries + [VariableBinder(name, type)])

    def with_typevar(self, name: Name, kind: Kind) -> TypingContext:
        return TypingContext(self.entries + [TypeBinder(name, kind)])

    def fresh_var(self):
        assert False, "Replace with fresh_counter"

    def kind_of(self, ty: Type) -> Kind:
        match ty:
            case BaseType(_) | Top() | RefinedType(
                _, BaseType(_), _) | RefinedType(_, TypeConstructor(_, _), _):
                return BaseKind()
            case TypeVar(name):
                assert (name, BaseKind()) in self.typevars()
                # TODO Polytypes: What it * is in context?
                return BaseKind()
            case RefinedType(_, TypeVar(name), _):
                assert (name, BaseKind()) in self.typevars(
                ), f"{name} not in {self.typevars()}"
                return BaseKind()
            case AbstractionType(_, _, _):
                return StarKind()
            case TypePolymorphism(_, _, _):
                return StarKind()
            case TypeConstructor(_, _):
                return BaseKind()
            case _:
                assert False, f"Unknown type in context: {ty}"

    def typevars(self) -> list[tuple[Name, Kind]]:
        return [ (e.type_name, e.type_kind) for e in self.entries if isinstance(e, TypeBinder) ]

    def vars(self) -> list[tuple[Name, Type]]:
        return [ (e.name, e.type) for e in self.entries if isinstance(e, VariableBinder) or isinstance(e, UninterpretedBinder) ]

    def concrete_vars(self) -> list[tuple[Name, Type]]:
        return [ (e.name, e.type) for e in self.entries if isinstance(e, VariableBinder) ]

    def get_type_constructor(self, name: Name) -> list[Name] | None:
        for entry in self.entries[::-1]:
            match entry:
                case TypeConstructorBinder(ename, eargs):
                    if ename == name:
                        return eargs
        # TODO: enter in context.
        if name.name in ["Unit", "Int", "Bool", "Float", "String"]:
            return []
        return None

    def __repr__(self):
        return "{" + ",".join(repr(e) for e in self.entries) + "}"

    def __hash__(self):
        return sum( hash(e) for e in self.entries  )
