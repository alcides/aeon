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
    def fresh_var(self):
        return "fresh_1"

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
