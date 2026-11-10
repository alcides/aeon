"""De Bruijn levels for grammar bindings, lowered to Aeon's named core.

Levels count value/predicate binders from the outside in and do not shift when
another binder is added. Grammar productions select a level; only the adapter
resolves it to a core variable. Generated binders receive fresh core identities
and distinct printable names, so named typechecking and surface round trips
cannot confuse nested instantiations of the same polymorphic signature.
"""

from __future__ import annotations

from dataclasses import dataclass

from aeon.core.substitutions import substitution_in_type
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, Type
from aeon.typechecking.context import (
    TypingContext,
    VariableBinder,
    UninterpretedBinder,
    ReflectedBinder,
    RefinementBinder,
)
from aeon.utils.name import Name, fresh_counter

_VALUE_BINDERS = (VariableBinder, UninterpretedBinder, ReflectedBinder)


@dataclass(frozen=True)
class BoundLevel:
    level: int

    def lower(self, scope: GrammarScope) -> tuple[Var, Type]:
        if not 0 <= self.level < len(scope.bindings):
            raise ValueError("grammar variable is outside its scope")
        binding = scope.bindings[self.level]
        if isinstance(binding, RefinementBinder):
            raise ValueError("logical predicates are not runtime grammar variables")
        return Var(binding.name), binding.type


@dataclass(frozen=True)
class GrammarScope:
    context: TypingContext
    bindings: tuple

    @classmethod
    def from_context(cls, context: TypingContext) -> GrammarScope:
        return cls(context, tuple(e for e in context.entries if isinstance(e, (*_VALUE_BINDERS, RefinementBinder))))

    def visible_levels(self) -> tuple[BoundLevel, ...]:
        # Preserve source-level shadowing/exclusions. Generated locals have
        # distinct printed names, so outer locals remain selectable by level.
        visible: dict[str, BoundLevel] = {}
        for level, entry in enumerate(self.bindings):
            if isinstance(entry, RefinementBinder):
                visible.pop(entry.name.name, None)
            else:
                visible[entry.name.name] = BoundLevel(level)
        return tuple(visible.values())

    def bind(self, hint: str, typ: Type) -> tuple[BoundLevel, GrammarScope]:
        level = BoundLevel(len(self.bindings))
        # Level alone is not a core identity: sibling branches have the same
        # depth. Allocate a fresh name for each lowering of a binder.
        name = Name(hint, fresh_counter.fresh())
        used = {e.name for e in self.bindings}
        while name in used or any(e.name.name == name.name for e in self.bindings):
            name = Name(f"{hint}_{level.level}_{fresh_counter.fresh()}", fresh_counter.fresh())
        context = self.context.with_var(name, typ)
        return level, GrammarScope(context, self.bindings + (VariableBinder(name, typ),))


def open_abstraction(typ: AbstractionType, context: TypingContext) -> tuple[Name, Type, TypingContext]:
    """Open a signature binder by level, renaming its dependent result type."""
    level, scope = GrammarScope.from_context(context).bind(typ.var_name.name, typ.var_type)
    variable, _ = level.lower(scope)
    body = substitution_in_type(typ.type, variable, typ.var_name)
    return variable.name, body, scope.context
