"""Expression nonterminals distinguish executable code from logical predicates."""

from dataclasses import dataclass
from enum import Enum

from aeon.core.types import (
    AbstractionType,
    RefinedType,
    RefinementPolymorphism,
    Type,
    TypeConstructor,
    TypePolymorphism,
    TypeVar,
)
from aeon.typechecking.context import (
    ReflectedBinder,
    RefinementBinder,
    TypingContext,
    UninterpretedBinder,
    VariableBinder,
)
from aeon.utils.name import Name


class ExpressionDomain(Enum):
    TERM = "term"
    REFINEMENT = "refinement"


@dataclass(frozen=True)
class Nonterminal:
    domain: ExpressionDomain
    type: Type


def _scalar(ty: Type) -> bool:
    if isinstance(ty, RefinedType):
        return _scalar(ty.type)
    if isinstance(ty, TypeConstructor):
        return all(_scalar(arg) for arg in ty.args)
    return isinstance(ty, TypeVar)


def _logical_signature(ty: Type) -> bool:
    """Logical applications are saturated and have first-order arguments."""
    while isinstance(ty, (TypePolymorphism, RefinementPolymorphism)):
        ty = ty.body
    while isinstance(ty, AbstractionType):
        if not _scalar(ty.var_type):
            return False
        ty = ty.type
    return _scalar(ty)


@dataclass(frozen=True)
class GrammarScope:
    terms: tuple[tuple[Name, Type], ...]
    refinements: tuple[tuple[Name, Type], ...]

    @classmethod
    def from_context(cls, ctx: TypingContext) -> "GrammarScope":
        """Resolve the nearest declaration before assigning any productions.

        A logical declaration shadows an outer runtime declaration in both
        domains. No production for that hidden declaration is ever created.
        Executable first-order values may participate in both domains.
        """
        seen: set[str] = set()
        terms: list[tuple[Name, Type]] = []
        refinements: list[tuple[Name, Type]] = []
        for entry in reversed(ctx.entries):
            if not isinstance(entry, (VariableBinder, ReflectedBinder, RefinementBinder, UninterpretedBinder)):
                continue
            if entry.name.name in seen:
                continue
            seen.add(entry.name.name)
            binding = (entry.name, entry.type)
            if isinstance(entry, (VariableBinder, ReflectedBinder)):
                terms.append(binding)
            if _logical_signature(entry.type):
                refinements.append(binding)
        return cls(tuple(reversed(terms)), tuple(reversed(refinements)))

    def bindings(self, domain: ExpressionDomain) -> tuple[tuple[Name, Type], ...]:
        return self.terms if domain is ExpressionDomain.TERM else self.refinements


def grammar_bindings(
    ctx: TypingContext, domain: ExpressionDomain = ExpressionDomain.TERM
) -> tuple[tuple[Name, Type], ...]:
    return GrammarScope.from_context(ctx).bindings(domain)
