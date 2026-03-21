from __future__ import annotations

from typing import Any

from aeon.decorators.api import Metadata, metadata_update
from aeon.sugar.program import Definition, STerm, SLiteral


def llvm(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    llvm_args: dict[str, Any] = {"llvm": True, "llvm_debug": False, "llvm_cache": False}

    arg_keys = ["llvm_debug", "llvm_cache"]

    for key, arg in zip(arg_keys, args):
        if isinstance(arg, SLiteral):
            llvm_args[key] = arg.value

    metadata = metadata_update(metadata, fun, llvm_args)
    return fun, [], metadata
