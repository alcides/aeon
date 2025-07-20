from __future__ import annotations

from abc import ABC
from dataclasses import dataclass, field
from typing import MutableSequence

from aeon.core.types import (
    AbstractionType,
    BaseKind,
    RefinedType,
    Top,
    TypeConstructor,
    TypePolymorphism,
    TypeVar,
    builtin_core_types,
)
from aeon.core.types import Kind
from aeon.core.types import StarKind
from aeon.core.types import Type
from aeon.utils.name import Name


class TypingContextEntry(ABC):
    pass


@dataclass(unsafe_hash=True)
class VariableBinder(TypingContextEntry):
    name: Name
    type: Type

    def __repr__(self):
        return f"{self.name} : {self.type}"


@dataclass
class UninterpretedBinder(TypingContextEntry):
    name: Name
    type: AbstractionType

    def __repr__(self):
        return f"uninterpreted {self.name} : {self.type}"


@dataclass
class TypeBinder(TypingContextEntry):
    type_name: Name
    type_kind: Kind = field(default_factory=StarKind)

    def __repr__(self):
        return f"type {self.type_name} {self.type_kind}"


@dataclass
class TypeConstructorBinder(TypingContextEntry):
    name: Name
    args: list[Name]  # cant hash

    def __repr__(self):
        if self.args:
            argsf = "(" + ", ".join(map(str, self.args)) + ")"
        else:
            argsf = ""
        return f"type {self.name}{argsf}"

    def __hash__(self):
        return hash(self.name) + hash(tuple(self.args))


@dataclass
class TypingContext:
    entries: MutableSequence[TypingContextEntry] = field(default_factory=list)

    def __post_init__(self):
        for bt in builtin_core_types[::-1]:
            temp = TypeConstructorBinder(bt.name, [])
            if temp not in self.entries:
                self.entries.insert(0, temp)

    def __repr__(self):
        fields = "; ".join(map(repr, self.entries))
        return f"[[{fields}]]"

    def with_var(self, name: Name, type: Type) -> TypingContext:
        nentries = [e for e in self.entries] + [VariableBinder(name, type)]
        return TypingContext(nentries)

    def with_typevar(self, name: Name, kind: Kind) -> TypingContext:
        nentries = [e for e in self.entries] + [TypeBinder(name, kind)]
        return TypingContext(nentries)

    def type_of(self, name: Name) -> Type | None:
        for e in self.entries:
            match e:
                case VariableBinder(iname, ty):
                    if iname == name:
                        return ty
        return None

    def kind_of(self, ty: Type) -> Kind:
        match ty:
            case Top() | RefinedType(_, TypeConstructor(_), _) | RefinedType(_, TypeConstructor(_, _), _):
                return BaseKind()
            case TypeVar(name):
                assert (name, BaseKind()) in self.typevars()
                # TODO Polytypes: What it * is in context?
                return BaseKind()
            case RefinedType(_, TypeVar(name), _):
                assert (name, BaseKind()) in self.typevars(), f"{name} not in {self.typevars()}"
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
        return [(e.type_name, e.type_kind) for e in self.entries if isinstance(e, TypeBinder)]

    def vars(self) -> list[tuple[Name, Type]]:
        return [
            (e.name, e.type)
            for e in self.entries
            if isinstance(e, VariableBinder) or isinstance(e, UninterpretedBinder)
        ]

    def concrete_vars(self) -> list[tuple[Name, Type]]:
        return [(e.name, e.type) for e in self.entries if isinstance(e, VariableBinder)]

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

    def __hash__(self):
        return sum(hash(e) for e in self.entries)
