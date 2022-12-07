from abc import ABC
import random
from typing import Tuple, List, Optional
from aeon.core.types import Kind, Type


class TypingContext(ABC):

    def type_of(self, name: str) -> Optional[Type]:
        return None

    def with_var(self, name: str, type: Type) -> "TypingContext":
        return VariableBinder(self, name, type)

    def with_typevar(self, name: str, kind: Kind) -> "TypingContext":
        return TypeBinder(self, name, kind)

    def fresh_var(self):
        return "fresh_"

    def typevars(self) -> List[Tuple[str, Kind]]:
        ...

    def vars(self) -> List[Tuple[str, Type]]:
        ...


class EmptyContext(TypingContext):

    def __init__(self):
        self.counter = 0

    def fresh_var(self):
        self.counter += 1
        return f"fresh_{self.counter}"

    def __repr__(self) -> str:
        return "ø"

    def typevars(self) -> List[Tuple[str, Kind]]:
        return []

    def vars(self) -> List[Tuple[str, Type]]:
        return []

    def __hash__(self) -> int:
        return 0


class VariableBinder(TypingContext):
    prev: TypingContext
    name: str
    type: Type

    def __init__(self, prev: TypingContext, name: str, type: Type):
        self.prev = prev
        self.name = name
        self.type = type
        assert isinstance(prev, TypingContext)
        assert name not in prev.vars()

    def type_of(self, name: str) -> Optional[Type]:
        if name == self.name:
            return self.type
        return self.prev.type_of(name)

    def fresh_var(self):
        p = int(self.prev.fresh_var().split("_")[-1])
        while True:
            name = "fresh_{}".format(p)
            if self.type_of(name) is None:
                break
            p += 1
        return name

    def __repr__(self) -> str:
        return "{},{}:{}".format(self.prev, self.name, self.type)

    def vars(self) -> List[Tuple[str, Type]]:
        return [(self.name, self.type)] + self.prev.vars()

    def typevars(self) -> List[Tuple[str, Kind]]:
        return self.prev.typevars()

    def __hash__(self) -> int:
        return hash(self.prev) + hash(self.name) + hash(self.type)


class TypeBinder(TypingContext):
    type_name: str
    type_kind: str

    def __init__(self, prev: TypingContext, type_name, type_kind="*"):
        self.prev = prev
        self.type_name = type_name
        self.type_kind = type_kind

    def type_of(self, name: str) -> Optional[Type]:
        return self.prev.type_of(name)

    def fresh_var(self):
        return self.prev.fresh_var()

    def vars(self) -> List[Tuple[str, Type]]:
        return self.prev.vars()

    def typevars(self) -> List[Tuple[str, Kind]]:
        return [(self.type_name, self.type_kind)] + self.prev.typevars()

    def __repr__(self) -> str:
        return "{},<{}:{}>".format(self.prev, self.type_name, self.type_kind)

    def __hash__(self) -> int:
        return hash(self.prev) + hash(self.type_name) + hash(self.type_kind)
