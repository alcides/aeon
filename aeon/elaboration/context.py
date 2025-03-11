from abc import ABC
from dataclasses import dataclass

from aeon.core.types import Kind
from aeon.sugar.program import TypeDecl
from aeon.sugar.stypes import SType


class TypingContextEntry(ABC):
    pass


@dataclass
class ElabVariableBinder(TypingContextEntry):
    name: str
    type: SType


@dataclass
class ElabUninterpretedBinder(TypingContextEntry):
    name: str
    type: SType


@dataclass
class ElabTypeVarBinder(TypingContextEntry):
    name: str
    type: Kind


@dataclass
class ElabTypeDecl(TypingContextEntry):
    name: str
    args: list[str]


@dataclass
class ElaborationTypingContext:
    entries: list[TypingContextEntry]

    def type_of(self, name: str):
        """Returns the type of the variable name."""
        for entry in self.entries[::-1]:
            match entry:
                case ElabVariableBinder(bname, ty):
                    if bname == name:
                        return ty
        return None

    def with_var(self, name: str, ty: SType):
        """Creates a new context, with an extra variable."""
        return ElaborationTypingContext(self.entries +
                                        [ElabVariableBinder(name, ty)])

    def with_typevar(self, name: str, kind: Kind):
        """Creates a new context, with an extra type variable"""
        return ElaborationTypingContext(self.entries +
                                        [ElabTypeVarBinder(name, kind)])

    def fresh_typevar(self) -> str:
        """Returns a type variable that does not exist in context."""
        i = 0
        while True:
            i += 1
            name = f"FreshT{i}"
            if name not in [
                    tvb.name for tvb in self.entries
                    if isinstance(tvb, ElabTypeVarBinder)
            ]:
                return name


def build_typing_context(
        ls: dict[str, SType],
        tdecl: list[TypeDecl] | None = None) -> ElaborationTypingContext:
    if tdecl is None:
        tdecl = []
    return ElaborationTypingContext(
        [ElabVariableBinder(name, ls[name])
         for name in ls] + [ElabTypeDecl(td.name, td.args) for td in tdecl])
