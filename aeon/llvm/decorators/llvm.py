from __future__ import annotations

from typing import Any

from aeon.core.terms import Term
from aeon.decorators.api import Metadata, metadata_update_by_name
from aeon.sugar.program import Decorator, SLiteral
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def _llvm_options_from_decorator(decorator: Decorator) -> dict[str, Any]:
    llvm_args: dict[str, Any] = {"llvm": True, "llvm_debug": False, "llvm_cache": False}

    arg_keys = ["llvm_debug", "llvm_cache"]

    for key, arg in zip(arg_keys, decorator.macro_args):
        if isinstance(arg, SLiteral):
            llvm_args[key] = arg.value

    mapping = {
        "debug": "llvm_debug",
        "cache": "llvm_cache",
    }
    for name, arg in decorator.named_args.items():
        key = mapping.get(name.name, name.name)
        if key in llvm_args and isinstance(arg, SLiteral):
            llvm_args[key] = arg.value
    return llvm_args


def llvm_core(
    decorator: Decorator,
    fun_name: Name,
    typing_ctx: TypingContext,
    core_program: Term,
    metadata: Metadata,
) -> Metadata:
    _ = typing_ctx, core_program
    return metadata_update_by_name(metadata, fun_name, _llvm_options_from_decorator(decorator))
