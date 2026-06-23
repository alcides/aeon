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


class AeonError(Exception):
    def __str__(self) -> str: ...

    def position(self) -> Location: ...


@dataclass
class ModuleNotFoundAeonError(AeonError):
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
        return (
            f"Could not infer a single type for {self.name}: it would need to be both "
            f"{self.conflict1} and {self.conflict2} simultaneously, but those two types are not compatible."
        )

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


@dataclass
class MethodResolutionError(AeonError):
    """Raised when a method-call ``receiver.method`` (issue #27) cannot be
    resolved: either the receiver's type is not concrete enough to pick a
    qualifier, or no ``Type.method`` definition exists for that type."""

    method: str
    type_name: str | None
    loc: Location

    def __str__(self) -> str:
        if self.type_name is None:
            return (
                f"Cannot resolve method call '.{self.method}': the receiver's type "
                f"could not be determined. Annotate the receiver to fix its type."
            )
        return f"No method '{self.method}' defined for type '{self.type_name}' (looked up '{self.type_name}.{self.method}')."

    def position(self) -> Location:
        return self.loc


@dataclass
class InstanceResolutionError(AeonError):
    class_name: str
    head: str | None
    loc: Location

    def __str__(self) -> str:
        target = self.head if self.head is not None else "<unknown>"
        return f"No instance found for class '{self.class_name}' on type '{target}'."

    def position(self) -> Location:
        return self.loc


@dataclass
class NonOrderableComparisonError(AeonError):
    """Raised when an ordered comparison (``<``, ``<=``, ``>``, ``>=``) is used
    at a type that has no ordering (issue #292). The builtin comparison
    operators are restricted to ``Int``, ``Float`` and ``String``; other types
    must define their own ordering via the ``Ord`` typeclass."""

    operator: str
    type_name: str
    loc: Location

    def __str__(self) -> str:
        return (
            f"Operator '{self.operator}' is not defined for type '{self.type_name}'; "
            f"ordered comparisons require Int, Float or String."
        )

    def position(self) -> Location:
        return self.loc


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
    """A ``1``-bound name was used more than once in its scope, either
    because it appears multiple times syntactically or because it was
    passed into a parameter whose multiplicity scales the use to ``ω``."""

    name: object
    declared: Multiplicity
    actual_uses: int
    term: Term
    use_locations: list[Location] = field(default_factory=list)
    cause: str = "syntactic"  # "syntactic" or "scaled-to-omega"

    def __str__(self) -> str:
        if self.cause == "scaled-to-omega":
            head = (
                f"Linear binding {self.name} is declared with multiplicity {self.declared} "
                f"but is consumed by an unrestricted parameter — its tally is scaled to ω."
            )
        else:
            head = (
                f"Linear binding {self.name} is declared with multiplicity {self.declared} "
                f"but is used {self.actual_uses} times."
            )
        if self.use_locations:
            locs = "; ".join(_format_location(loc) for loc in self.use_locations)
            return f"{head} Uses at: {locs}."
        return head

    def position(self) -> Location:
        # Point at the first offending use rather than the binder — that's
        # what the user is actively fixing.
        if self.use_locations:
            return self.use_locations[0]
        return self.term.loc


@dataclass
class ErasedUsedAtRuntimeError(LinearityError):
    """A ``0``-bound name was referenced from a runtime position. ``0`` is
    intended for proof-only / ghost bindings — referencing it here would
    require it at evaluation time."""

    name: object
    term: Term
    use_locations: list[Location] = field(default_factory=list)

    def __str__(self) -> str:
        head = f"Erased binding {self.name} (multiplicity 0) cannot be used at runtime."
        if self.use_locations:
            locs = "; ".join(_format_location(loc) for loc in self.use_locations)
            return f"{head} Used at: {locs}."
        return head

    def position(self) -> Location:
        if self.use_locations:
            return self.use_locations[0]
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
    then_locations: list[Location] = field(default_factory=list)
    else_locations: list[Location] = field(default_factory=list)

    def __str__(self) -> str:
        head = (
            f"Linear binding {self.name} is used {self.then_uses} time(s) in the `then` branch "
            f"but {self.else_uses} time(s) in the `else` branch — both branches must consume it equally."
        )
        parts = []
        if self.then_locations:
            parts.append("then-uses at: " + "; ".join(_format_location(loc) for loc in self.then_locations))
        if self.else_locations:
            parts.append("else-uses at: " + "; ".join(_format_location(loc) for loc in self.else_locations))
        if parts:
            return head + " " + " ".join(parts) + "."
        return head

    def position(self) -> Location:
        return self.term.loc


def _format_location(loc: Location) -> str:
    """Render a ``Location`` as a short, user-readable ``file:line:col``
    pair when we have positional info; otherwise fall back to ``str``."""
    file = getattr(loc, "file", "")
    start = getattr(loc, "start", None)
    if start is not None:
        line, col = start[0], start[1]
        prefix = f"{file}:" if file else ""
        return f"{prefix}{line}:{col}"
    return str(loc)
