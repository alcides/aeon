from __future__ import annotations

from abc import ABC
from copy import copy
from dataclasses import dataclass

from aeon.core.types import AbstractionType, BaseKind, BaseType, Bottom, RefinedType, Top, TypePolymorphism, TypeVar
from aeon.core.types import Kind
from aeon.core.types import StarKind
from aeon.core.types import Type


class TypingContextEntry(ABC):
    pass


@dataclass
class VariableBinder(TypingContextEntry):
    name: str
    type: Type

    def __str__(self):
        return f"{self.name}:{self.type}"


@dataclass
class TypeBinder(TypingContextEntry):
    name: str
    kind: Kind

    def __str__(self):
        return f"{self.name}:{self.kind}"


@dataclass
class UninterpretedFunctionBinder(TypingContextEntry):
    name: str
    type: AbstractionType

    def __str__(self):
        return f"fun {self.name}:{self.type}"


class TypingContext:
    """Represents the Typing Context of the program at a given point."""

    entries: list[TypingContextEntry]

    def __init__(self, entries=None):
        self.entries = copy(entries) if entries else []

    def __add__(self, other):
        return TypingContext(self.entries + [other])

    def __str__(self):
        return "ø" + ", ".join(str(e) for e in self.entries)

    def type_of(self, name: str) -> Type | None:
        candidates = [
            te for te in self.entries
            if isinstance(te, VariableBinder) and te.name == name
        ]
        return candidates[-1].type if candidates else None

    def with_var(self, name: str, type: Type) -> TypingContext:
        return self + VariableBinder(name, type)

    def with_typevar(self, name: str, kind: Kind) -> TypingContext:
        return self + TypeBinder(name, kind)

    def typevars(self) -> list[tuple[str, Kind]]:
        return [(te.name, te.kind) for te in self.entries
                if isinstance(te, TypeBinder)]

    def vars(self) -> list[tuple[str, Type]]:
        return [(te.name, te.type) for te in self.entries
                if isinstance(te, VariableBinder)]

    def fresh_var(self):
        x = len(self.entries)
        return f"fresh_{x}"

    def kind_of(self, ty) -> Kind | None:
        if isinstance(ty, BaseType):
            return BaseKind()
        elif isinstance(ty, Top):
            return BaseKind()
        elif isinstance(ty, Bottom):
            return BaseKind()
        elif isinstance(ty, RefinedType) and not isinstance(ty.type, TypeVar):
            return BaseKind()
        elif isinstance(ty, TypePolymorphism):
            return StarKind()
        elif isinstance(ty, AbstractionType):
            return StarKind()
        elif isinstance(ty, TypeVar):
            for t, k in self.typevars():
                if t == ty:
                    return k
            return None
        elif isinstance(ty, RefinedType) and isinstance(ty.type, TypeVar):
            assert (ty.type, BaseKind()) in self.typevars()
            return BaseKind()
        else:
            assert False
