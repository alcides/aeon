"""Modular verification conditions (VC) for liquid typechecking of **fragments**.

This is intentionally **not** ``check_type``: callers get the intermediate
``Constraint`` produced by ``check`` *before* a single closed-world entailment
step, and may inspect it, feed it to ``constraint_to_parts``, or call
``solve`` with a custom finite qualifier set **Q** while still reusing
``entailment_context`` and Horn infrastructure.

Caveat: ``check`` still invokes ``check_type`` in a few internal spots (notably
``if`` conditions) for soundness; those sub-checks are not returned as separate
``ModularVC`` objects without a larger refactor.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass

from aeon.core.liquid import LiquidTerm
from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.facade.api import CoreWellformnessError
from aeon.typechecking.context import TypingContext
from aeon.typechecking.entailment import entailment, entailment_context
from aeon.typechecking.typeinfer import check, constraint_to_parts
from aeon.typechecking.well_formed import wellformed
from aeon.utils.location import Location
from aeon.verification.horn import solve
from aeon.verification.vcs import Constraint


@dataclass(frozen=True, slots=True)
class ModularVC:
    """VC for ``context ⊢ term : expected`` (constraint from ``check`` only)."""

    context: TypingContext
    term: Term
    expected: Type
    constraint: Constraint

    @property
    def lifted(self) -> Constraint:
        """``constraint`` after ``entailment_context`` (binder lifting for Horn)."""
        return entailment_context(self.context, self.constraint)

    def entails(self) -> bool:
        """Closed-world validity: same answer as ``check_type(context, term, expected)`` when both succeed."""
        return entailment(self.context, self.constraint)

    def entails_with_qualifiers(
        self,
        qualifier_atoms: frozenset[LiquidTerm],
        *,
        typing_ctx: TypingContext | None = None,
    ) -> bool:
        """Solve the lifted VC with an explicit **Q** (and optional typing context for prelude)."""
        tctx = typing_ctx if typing_ctx is not None else self.context
        return solve(self.lifted, typing_ctx=tctx, qualifier_atoms=qualifier_atoms)

    def explain_failures(
        self,
        typing_ctx: TypingContext | None = None,
    ) -> Iterable[tuple[Constraint, Location | None]]:
        """Yield failing Horn-style fragments (meaningful when ``entails()`` is false)."""
        return constraint_to_parts(self.lifted, typing_ctx if typing_ctx is not None else self.context)


def build_modular_vc(ctx: TypingContext, term: Term, expected: Type) -> ModularVC:
    """Build the VC for ``ctx ⊢ term : expected`` via ``check`` (no entailment yet).

    Raises the same ``CoreWellformnessError`` / ``CoreTypeCheckingError`` family
    as ``check_type`` when the fragment does not typecheck structurally.
    """
    if not wellformed(ctx, expected):
        raise CoreWellformnessError(expected)
    c = check(ctx, term, expected)
    return ModularVC(context=ctx, term=term, expected=expected, constraint=c)
