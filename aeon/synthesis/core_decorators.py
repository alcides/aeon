"""Decorators registered with ``DecoratorPhase.CORE`` (see ``aeon.decorators``).

These run after elaboration, lowering, and typechecking. The surface syntax is
unchanged: ``@name(...)`` — only the Python registration picks the phase.
"""

from __future__ import annotations

from aeon.core.terms import Term
from aeon.decorators.api import CoreDecoratorType, Metadata, metadata_update_by_name
from aeon.llvm.decorators.gpu import gpu_core
from aeon.llvm.decorators.llvm import llvm_core
from aeon.sugar.program import Decorator
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def dp_decorator(dec, fun_name, typing_ctx, program, metadata):
    from aeon.synthesis.modules.dp_gp.source import dp_decorator as apply_dp

    return apply_dp(dec, fun_name, typing_ctx, program, metadata)


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
    "dp_gp": dp_decorator,
    "after_typecheck": after_typecheck,
    "llvm": llvm_core,
    "gpu": gpu_core,
}
