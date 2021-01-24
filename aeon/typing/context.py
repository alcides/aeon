import typing
from typing import Optional
from aeon.core.types import AbstractionType, Type


class TypingContext(object):
    def type_of(self, name: str) -> Optional[Type]:
        return None

    def with_var(self, name: str, type: Type) -> "TypingContext":
        return VariableBinder(self, name, type)

    def fresh_var(self):
        return "#_"


class EmptyContext(TypingContext):
    def fresh_var(self):
        return "#_1"

    def __repr__(self) -> str:
        return "ø"


class VariableBinder(TypingContext):
    prev: TypingContext
    name: str
    type: Type

    def __init__(self, prev: TypingContext, name: str, type: Type):
        self.prev = prev
        self.name = name
        self.type = type

    def type_of(self, name: str) -> Optional[Type]:
        if name == self.name:
            return self.type
        return self.prev.type_of(name)

    def fresh_var(self):
        p = int(self.prev.fresh_var().split("_")[-1])
        while self.type_of(p):
            p += 1
        return "#_{}".format(p)

    def __repr__(self) -> str:
        return "{},{}:{}".format(self.prev, self.name, self.type)