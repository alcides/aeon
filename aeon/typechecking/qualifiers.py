"""Extract finite qualifier sets (Q) from typing context and types.

Used for predicate abstraction / constrained Horn solving: unknown refinements
are searched as boolean combinations of atoms drawn from Q (see e.g. Jhala &
Vazou, "Refinement Types: A Tutorial", arXiv:2010.07763; Polikarpova et al.,
PLDI 2016 Synquid).
"""

from __future__ import annotations

from aeon.core.liquid import LiquidTerm
from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.typechecking.context import (
    TypeBinder,
    TypeConstructorBinder,
    TypingContext,
    UninterpretedBinder,
    VariableBinder,
)
from aeon_rs import collect_from_term as _collect_from_term
from aeon_rs import collect_from_type as _collect_from_type


def extract_qualifier_atoms(
    ctx: TypingContext,
    goal_type: Type | None = None,
    term: Term | None = None,
    *,
    max_atoms: int = 512,
) -> frozenset[LiquidTerm]:
    """Finite set Q of boolean liquid atoms from refinements in scope.

    Sources: variable and uninterpreted bindings in ``ctx``, optional
    ``goal_type``, and optional ``term`` (annotations and nested types).
    If more than ``max_atoms`` are found, the set is truncated deterministically.
    """
    sink: set[LiquidTerm] = set()
    for e in ctx.entries:
        match e:
            case VariableBinder(_, ty) | UninterpretedBinder(_, ty):
                _collect_from_type(ty, sink)
            case TypeBinder() | TypeConstructorBinder():
                pass
            case _:
                pass
    if goal_type is not None:
        _collect_from_type(goal_type, sink)
    if term is not None:
        _collect_from_term(term, sink)
    if len(sink) <= max_atoms:
        return frozenset(sink)
    ordered = sorted(sink, key=repr)
    return frozenset(ordered[:max_atoms])
