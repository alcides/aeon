"""Decorators registered with ``DecoratorPhase.CORE`` (see ``aeon.decorators``).

These run after elaboration, lowering, ANF conversion, and typechecking. The
surface syntax is unchanged: ``@name(...)`` — only the Python registration picks
the phase.
"""

from __future__ import annotations

from aeon.core.terms import Term
from aeon.decorators.api import CoreDecoratorType, Metadata, metadata_update_by_name
from aeon.llvm.decorators.gpu import gpu_core
from aeon.llvm.decorators.cpu import cpu_core
from aeon.sugar.program import Decorator
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def after_typecheck(
    dec: Decorator,
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
    assert len(dec.macro_args) == 0, "after_typecheck expects no arguments"
    _ = typing_ctx, core_program
    return metadata_update_by_name(metadata, fun_name, {"ran_after_typecheck": True})


core_decorators_environment: dict[str, CoreDecoratorType] = {
    "after_typecheck": after_typecheck,
    "cpu": cpu_core,
    "gpu": gpu_core,
}
