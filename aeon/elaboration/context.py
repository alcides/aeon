from abc import ABC
from dataclasses import dataclass

from aeon.core.types import Kind
from aeon.sugar.program import TypeDecl
from aeon.sugar.stypes import SType
from aeon.utils.name import Name, fresh_counter


class ElabTypingContextEntry(ABC):
    pass


@dataclass
class ElabVariableBinder(ElabTypingContextEntry):
    name: Name
    type: SType


@dataclass
class ElabUninterpretedBinder(ElabTypingContextEntry):
    name: Name
    type: SType


@dataclass
class ElabTypeVarBinder(ElabTypingContextEntry):
    name: Name
    type: Kind


@dataclass
class ElabTypeDecl(ElabTypingContextEntry):
    name: Name
    args: list[Name]


@dataclass
class ElaborationTypingContext:
    entries: list[ElabTypingContextEntry]

    def type_of(self, name: Name):
        """Returns the type of the variable name."""
        for entry in self.entries[::-1]:
            match entry:
                case ElabVariableBinder(bname, ty):
                    if bname == name:
                        return ty
        return None

    def with_var(self, name: Name, ty: SType):
        """Creates a new context, with an extra variable."""
        return ElaborationTypingContext(self.entries +
                                        [ElabVariableBinder(name, ty)])

    def with_typevar(self, name: Name, kind: Kind):
        """Creates a new context, with an extra type variable"""
        return ElaborationTypingContext(self.entries +
                                        [ElabTypeVarBinder(name, kind)])

    def fresh_typevar(self) -> Name:
        """Returns a type variable that does not exist in context."""
        i = 0
        while True:
            i += 1
            name = Name("fresh", fresh_counter.fresh())
            if name not in [
                    tvb.name for tvb in self.entries
                    if isinstance(tvb, ElabTypeVarBinder)
            ]:
                return name


def build_typing_context(
        ls: dict[Name, SType],
        tdecl: list[TypeDecl] | None = None) -> ElaborationTypingContext:
    if tdecl is None:
        tdecl = []
    return ElaborationTypingContext(
        [ElabVariableBinder(name, ls[name])
         for name in ls] + [ElabTypeDecl(td.name, td.args) for td in tdecl])
