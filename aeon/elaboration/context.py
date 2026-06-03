from abc import ABC
from dataclasses import dataclass, field
from typing import MutableSequence

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
    rforalls: list[tuple[Name, SType]] = field(default_factory=list)


@dataclass
class ElaborationTypingContext:
    entries: MutableSequence[ElabTypingContextEntry] = field(default_factory=list)
    constructor_to_type: dict[str, Name] = field(default_factory=dict)
    constructor_defs: dict[str, Name] = field(default_factory=dict)
    # Instance-implicit ("given") constraints in lexical scope, as
    # ``(dict_variable_name, class_type)`` pairs — e.g. the ``[_c : Eq a]``
    # parameter of a constrained instance dictionary. Method calls on the
    # constrained type variable resolve to these before the global registry.
    instances: list[tuple[Name, SType]] = field(default_factory=list)

    def type_of(self, name: Name):
        """Returns the type of the variable name. Looks up regular bindings
        and uninterpreted-def bindings (uninterpreted measures like Array's
        ``size`` show up in the latter)."""
        for entry in self.entries[::-1]:
            match entry:
                case ElabVariableBinder(bname, ty) | ElabUninterpretedBinder(bname, ty):
                    if bname.name == name.name:
                        return ty
        return None

    def resolve_method(self, method: str, type_name: str) -> Name | None:
        """Resolve a method call ``receiver.method`` (issue #27) to the bound
        ``Name`` of the ``type_name.method`` definition, given the receiver's
        base type ``type_name``. Returns the actual in-scope ``Name`` (carrying
        its unique id, so the produced reference lowers to the right core
        binder) or ``None`` if no such definition exists.

        The lookup is by the fully-qualified string ``"Type.method"`` — which is
        exactly how a ``def Type.method`` is named — scanning the most recent
        binding first so locals shadow globals consistently with ``type_of``.
        """
        candidate = f"{type_name}.{method}"
        for entry in self.entries[::-1]:
            match entry:
                case ElabVariableBinder(bname, _) | ElabUninterpretedBinder(bname, _):
                    if bname.name == candidate:
                        return bname
        return None

    def with_var(self, name: Name, ty: SType):
        """Creates a new context, with an extra variable."""
        nentries = [x for x in self.entries] + [ElabVariableBinder(name, ty)]
        return ElaborationTypingContext(nentries, self.constructor_to_type, self.constructor_defs, self.instances)

    def with_typevar(self, name: Name, kind: Kind):
        """Creates a new context, with an extra type variable"""
        nentries = [x for x in self.entries] + [ElabTypeVarBinder(name, kind)]
        return ElaborationTypingContext(nentries, self.constructor_to_type, self.constructor_defs, self.instances)

    def with_instance(self, name: Name, class_type: SType):
        """Creates a new context with an extra in-scope given constraint."""
        ninstances = [x for x in self.instances] + [(name, class_type)]
        return ElaborationTypingContext(self.entries, self.constructor_to_type, self.constructor_defs, ninstances)

    def fresh_typevar(self) -> Name:
        """Returns a type variable that does not exist in context."""
        return Name("tv", fresh_counter.fresh())


def build_typing_context(
    ls: dict[Name, SType],
    tdecl: list[TypeDecl] | None = None,
    constructor_to_type: dict[str, Name] | None = None,
    constructor_defs: dict[str, Name] | None = None,
) -> ElaborationTypingContext:
    if tdecl is None:
        tdecl = []
    if constructor_to_type is None:
        constructor_to_type = {}
    if constructor_defs is None:
        constructor_defs = {}
    return ElaborationTypingContext(
        [ElabVariableBinder(name, ls[name]) for name in ls]
        + [ElabTypeDecl(td.name, td.args, td.rforalls) for td in tdecl],
        constructor_to_type,
        constructor_defs,
    )
