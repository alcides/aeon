from __future__ import annotations

from abc import ABC
from abc import abstractmethod
from dataclasses import dataclass

from aeon.core.types import AbstractionType, BaseKind, BaseType, Bottom, RefinedType, Top, TypePolymorphism, TypeVar
from aeon.core.types import Kind
from aeon.core.types import StarKind
from aeon.core.types import Type


class TypingContext(ABC):

    def type_of(self, name: str) -> Type | None:
        assert False

    def with_var(self, name: str, type: Type) -> TypingContext:
        return VariableBinder(self, name, type)

    def with_typevar(self, name: str, kind: Kind) -> TypingContext:
        return TypeBinder(self, name, kind)

    def fresh_var(self):
        if not hasattr(self, "global_counter"):
            self.global_counter = 0
        self.global_counter += 1
        return f"fresh_{self.global_counter}"

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

    @abstractmethod
    def typevars(self) -> list[tuple[str, Kind]]:
        ...

    @abstractmethod
    def vars(self) -> list[tuple[str, Type]]:
        ...


class EmptyContext(TypingContext):

    def __init__(self):
        self.counter = 0

    def type_of(self, name: str) -> Type | None:
        return None

    def __repr__(self) -> str:
        return "ø"

    def typevars(self) -> list[tuple[str, Kind]]:
        return []

    def vars(self) -> list[tuple[str, Type]]:
        return []

    def __hash__(self) -> int:
        return 0


@dataclass
class UninterpretedBinder(TypingContext):
    prev: TypingContext
    name: str
    type: AbstractionType

    def type_of(self, name: str) -> Type | None:
        if name == self.name:
            return self.type
        return self.prev.type_of(name)

    def fresh_var(self):
        name = self.name
        while name == self.name:
            name = self.prev.fresh_var()
        return name

    def __repr__(self) -> str:
        return f"{self.prev},{self.name}:{self.type}"

    def vars(self) -> list[tuple[str, Type]]:
        return [(self.name, self.type)] + self.prev.vars()

    def typevars(self) -> list[tuple[str, Kind]]:
        return self.prev.typevars()

    def __hash__(self) -> int:
        return hash(self.prev) + hash(self.name) + hash(self.type)


@dataclass(init=False)
class VariableBinder(TypingContext):
    prev: TypingContext
    name: str
    type: Type

    def __init__(self, prev: TypingContext, name: str, type: Type):
        self.prev = prev
        self.name = name
        self.type = type
        assert isinstance(prev, TypingContext)
        assert isinstance(type, Type)
        assert name not in prev.vars()

    def type_of(self, name: str) -> Type | None:
        if name == self.name:
            return self.type
        return self.prev.type_of(name)

    def fresh_var(self):
        name = self.name
        while name == self.name:
            name = self.prev.fresh_var()
        return name

    def __repr__(self) -> str:
        return f"{self.prev},{self.name}:{self.type}"

    def vars(self) -> list[tuple[str, Type]]:
        return [(self.name, self.type)] + self.prev.vars()

    def typevars(self) -> list[tuple[str, Kind]]:
        return self.prev.typevars()

    def __hash__(self) -> int:
        return hash(self.prev) + hash(self.name) + hash(self.type)


@dataclass(init=False)
class TypeBinder(TypingContext):
    prev: TypingContext
    type_name: str
    type_kind: Kind

    def __init__(
            self,
            prev: TypingContext,
            type_name: str,
            type_kind: Kind = StarKind(),
    ):
        self.prev = prev
        self.type_name = type_name
        self.type_kind = type_kind

    def type_of(self, name: str) -> Type | None:
        return self.prev.type_of(name)

    def fresh_var(self):
        name = self.type_name
        while name == self.type_name:
            name = self.prev.fresh_var()
        return name

    def vars(self) -> list[tuple[str, Type]]:
        return self.prev.vars()

    def typevars(self) -> list[tuple[str, Kind]]:
        return [(self.type_name, self.type_kind)] + self.prev.typevars()

    def __repr__(self) -> str:
        return f"{self.prev},<{self.type_name}:{self.type_kind}>"

    def __hash__(self) -> int:
        return hash(self.prev) + hash(self.type_name) + hash(self.type_kind)
