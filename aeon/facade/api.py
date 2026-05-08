from abc import ABC
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

from aeon.core.multiplicity import Multiplicity
from aeon.core.terms import Term
from aeon.core.types import Kind, Type
from aeon.sugar.program import ImportAe, STerm
from aeon.sugar.stypes import SType
from aeon.typechecking.context import TypingContext
from aeon.utils.location import Location
from aeon.verification.vcs import Constraint
from aeon.verification.helpers import pretty_print_constraint


class AeonError(ABC, BaseException):
    def __str__(self) -> str: ...

    def position(self) -> Location: ...


@dataclass
class ImportError(AeonError):
    importel: ImportAe
    possible_containers: Iterable[Path]

    def __str__(self) -> str:
        return f"Could not find module '{self.importel.module_path}' (file: {self.importel.file_path}) in the following list of container folders: {self.possible_containers}"

    def position(self) -> Location:
        return self.importel.loc


@dataclass
class UnificationSubtypingError(AeonError):
    expr: STerm
    subtype: SType
    suptype: SType
    msg: str = field(default_factory=lambda: "")

    def __str__(self) -> str:
        return (
            f"Expression {self.expr} has type {self.subtype}, but is expected to have type {self.suptype} ({self.msg})."
        )

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
class LiquidTypeCheckingFailedRelation(CoreTypeCheckingError):
    ctx: TypingContext
    term: Term
    type: Type
    vc: Constraint
    loc: Location | None = None

    def __str__(self) -> str:
        return f"Failed to prove ({pretty_print_constraint(self.vc)}) in {self.position()}"

    def position(self) -> Location:
        return self.loc if self.loc is not None else self.term.loc


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


# Linearity / quantitative type theory diagnostics.
#
# These fire when a binder declares a non-default multiplicity (`0` or `1`)
# and the body's syntactic uses of that name don't match. ``MOmega`` binders
# (the default for every existing program) are never reported.


class LinearityError(CoreTypeCheckingError):
    """Marker base for usage-discipline violations under QTT."""

    pass


@dataclass
class LinearUnusedError(LinearityError):
    """A ``1``-bound name was never referenced in its scope."""

    name: object  # Name; left as object to avoid an import cycle
    declared: Multiplicity
    term: Term

    def __str__(self) -> str:
        return f"Linear binding {self.name} is declared with multiplicity {self.declared} but is never used."

    def position(self) -> Location:
        return self.term.loc


@dataclass
class LinearUsedTooManyTimesError(LinearityError):
    """A ``1``-bound name was used more than once in its scope."""

    name: object
    declared: Multiplicity
    actual_uses: int
    term: Term

    def __str__(self) -> str:
        return (
            f"Linear binding {self.name} is declared with multiplicity {self.declared} "
            f"but is used {self.actual_uses} times."
        )

    def position(self) -> Location:
        return self.term.loc


@dataclass
class ErasedUsedAtRuntimeError(LinearityError):
    """A ``0``-bound name was referenced from a runtime position. ``0`` is
    intended for proof-only / ghost bindings — referencing it here would
    require it at evaluation time."""

    name: object
    term: Term

    def __str__(self) -> str:
        return f"Erased binding {self.name} (multiplicity 0) cannot be used at runtime."

    def position(self) -> Location:
        return self.term.loc


@dataclass
class LinearBranchMismatchError(LinearityError):
    """The two branches of an ``if`` use a ``1``-bound name a different
    number of times. Whichever branch is taken at run time, exactly one
    use must happen."""

    name: object
    then_uses: int
    else_uses: int
    term: Term

    def __str__(self) -> str:
        return (
            f"Linear binding {self.name} is used {self.then_uses} time(s) in the `then` branch "
            f"but {self.else_uses} time(s) in the `else` branch — both branches must consume it equally."
        )

    def position(self) -> Location:
        return self.term.loc
