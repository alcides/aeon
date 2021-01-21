import typing
from typing import Optional
from aeon.core.types import Type


class TypingContext(object):
    def type_of(self, name: str) -> Optional[Type]:
        return None

    def with_var(self, name: str, type: Type) -> typing.Type["VariableBinder"]:
        return VariableBinder(self, name, type)


class EmptyContext(TypingContext):
    pass


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
