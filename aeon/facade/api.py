from abc import ABC
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

from aeon.core.terms import Term
from aeon.core.types import Kind, Type
from aeon.sugar.program import ImportAe, STerm
from aeon.sugar.stypes import SType
from aeon.typechecking.context import TypingContext
from aeon.utils.location import Location
from aeon.utils.pprint import stype_pretty


class AeonError(ABC, BaseException):
    def __str__(self) -> str: ...

    def position(self) -> Location: ...


@dataclass
class ImportError(AeonError):
    importel: ImportAe
    possible_containers: Iterable[Path]

    def __str__(self) -> str:
        return f"Could not find {self.importel.path} in the following list of container folders: {self.possible_containers}"

    def position(self) -> Location:
        return self.importel.loc


@dataclass
class UnificationSubtypingError(AeonError):
    expr: STerm
    subtype: SType
    suptype: SType
    msg: str = field(default_factory=lambda: "")

    def __str__(self) -> str:
        return f"Expression {self.expr} has type {stype_pretty(self.subtype)}, but is expected to have type {stype_pretty(self.suptype)} ({self.msg})."

    def position(self) -> Location:
        return self.expr.loc


@dataclass
class UnificationFailedError(AeonError):
    name: str
    conflict1: SType
    conflict2: SType

    def __str__(self) -> str:
        return f"Unification variable {self.name} needs to be {self.conflict1} and {self.conflict2} simultaneously, but the two types are not compatible."

    def position(self) -> Location:
        return self.conflict1.loc


@dataclass
class UnificationKindError(AeonError):
    term: STerm
    type: SType
    kind1: Kind
    kind2: Kind

    def __str__(self) -> str:
        return f"Term {self.term} has type {self.type} with kind {self.kind1}, but kind {self.kind2} is expected."

    def position(self) -> Location:
        return self.term.loc


@dataclass
class UnificationUnknownTypeError(AeonError):
    term: STerm

    def __str__(self) -> str:
        return f"Variable {self.term} does not exist in context."

    def position(self) -> Location:
        return self.term.loc


class CoreTypeCheckingError(AeonError):
    pass


@dataclass
class CoreWellformnessError(CoreTypeCheckingError):
    type: Type

    def __str__(self) -> str:
        return f"Type {self.type} is not well formed."

    def position(self) -> Location:
        return self.type.loc


@dataclass
class CoreTypingRelation(CoreTypeCheckingError):
    ctx: TypingContext
    term: Term
    type: Type

    def __str__(self) -> str:
        return f"Term {self.term} is not of expected type {self.type}."

    def position(self) -> Location:
        return self.term.loc


@dataclass
class CoreVariableNotInContext(CoreTypeCheckingError):
    ctx: TypingContext
    term: Term

    def __str__(self) -> str:
        return f"Variable {self.term} is not in context."

    def position(self) -> Location:
        return self.term.loc


@dataclass
class CoreInvalidApplicationError(CoreTypeCheckingError):
    term: Term
    type: Type

    def __str__(self) -> str:
        return f"Function application requires that {self.term} is a function, but it has type {self.type}."

    def position(self) -> Location:
        return self.term.loc


@dataclass
class CoreTypeApplicationRequiresBareTypesError(CoreTypeCheckingError):
    term: Term
    type: Type

    def __str__(self) -> str:
        return f"Type application requires that {self.term} of type {self.type} has a bare kind."

    def position(self) -> Location:
        return self.term.loc


@dataclass
class CoreWrongKindInTypeApplicationError(CoreTypeCheckingError):
    term: Term
    type: Type
    expected_kind: Kind
    actual_kind: Kind

    def __str__(self) -> str:
        return f"Type application requires that {self.term} of type {self.type} has kind {self.expected_kind}, but {self.actual_kind} was found."

    def position(self) -> Location:
        return self.term.loc


@dataclass
class CoreSubtypingError(CoreTypeCheckingError):
    ctx: TypingContext
    term: Term
    inferred_type: Type
    expected_type: Type

    def __str__(self) -> str:
        return f"Expression {self.term} is expected to be of type {self.expected_type}, but {self.inferred_type} was found instead."

    def position(self) -> Location:
        return self.term.loc
