import random
from typing import Tuple, List, Optional
from aeon.core.types import Type


class TypingContext(object):
    def type_of(self, name: str) -> Optional[Type]:
        return None

    def with_var(self, name: str, type: Type) -> "TypingContext":
        return VariableBinder(self, name, type)

    def fresh_var(self):
        return "fresh_"

    def vars(self) -> List[Tuple[str, Type]]:
        return []


class EmptyContext(TypingContext):
    def __init__(self):
        self.counter = 0

    def fresh_var(self):
        self.counter += 1
        return f"fresh_{self.counter}"

    def __repr__(self) -> str:
        return "ø"

    def vars(self) -> List[Tuple[str, Type]]:
        return []


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
        while self.type_of(p) is not None:
            p += 1
        return "fresh_{}".format(p)

    def __repr__(self) -> str:
        return "{},{}:{}".format(self.prev, self.name, self.type)

    def vars(self) -> List[Tuple[str, Type]]:
        return [(self.name, self.type)] + self.prev.vars()


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

    def __repr__(self) -> str:
        return "{},<{}:{}>".format(self.prev, self.type_name, self.type_kind)
