"""Decorators registered with ``DecoratorPhase.CORE`` (see ``aeon.decorators``).

These run after elaboration, lowering, ANF conversion, and typechecking. The
surface syntax is unchanged: ``@name(...)`` — only the Python registration picks
the phase.
"""

from __future__ import annotations

from aeon.core.terms import Term
from aeon.decorators.api import CoreDecoratorType, Metadata, metadata_update_by_name
from aeon.sugar.program import STerm
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def after_typecheck(
    args: list[STerm],
    fun_name: Name,
    typing_ctx: TypingContext,
    core_program: Term,
    metadata: Metadata,
) -> Metadata:
    """Example core-phase hook: records that the decorator ran (for tests and tooling).

    Usage (macro arguments are optional; empty ``()`` is not valid surface syntax)::

        @after_typecheck
        def f(x: Int) : Int = x + 1;
    """
    assert len(args) == 0, "after_typecheck expects no arguments"
    _ = typing_ctx, core_program
    return metadata_update_by_name(metadata, fun_name, {"ran_after_typecheck": True})


core_decorators_environment: dict[str, CoreDecoratorType] = {
    "after_typecheck": after_typecheck,
}
