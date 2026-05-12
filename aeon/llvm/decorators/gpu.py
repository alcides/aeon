from __future__ import annotations

from typing import Any

from aeon.core.terms import Term
from aeon.decorators.api import Metadata, metadata_update_by_name
from aeon.llvm.constants import LLVMMetadataKey
from aeon.sugar.program import Decorator, SLiteral
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def _gpu_options_from_decorator(decorator: Decorator) -> dict[str, Any]:
    gpu_info: dict[str, Any] = {
        LLVMMetadataKey.GPU_ENABLED.value: True,
    }

    mapping = {
        "device": LLVMMetadataKey.GPU_DEVICE.value,
        "target": LLVMMetadataKey.GPU_ARCH.value,
        "opt_level": LLVMMetadataKey.GPU_OPT_LEVEL.value,
        "debug": LLVMMetadataKey.GPU_DEBUG.value,
        "block_size": LLVMMetadataKey.GPU_BLOCK_SIZE.value,
        "arch": LLVMMetadataKey.GPU_ARCH.value,
    }
    allowed_keys = set(mapping.values())

    arg_keys = [
        LLVMMetadataKey.GPU_DEVICE.value,
        LLVMMetadataKey.GPU_ARCH.value,
        LLVMMetadataKey.GPU_OPT_LEVEL.value,
        None,
        LLVMMetadataKey.GPU_DEBUG.value,
        None,
        LLVMMetadataKey.GPU_BLOCK_SIZE.value,
        None,
    ]
    for key, arg in zip(arg_keys, decorator.macro_args):
        if key is not None and isinstance(arg, SLiteral):
            gpu_info[key] = arg.value

    for name, arg in decorator.named_args.items():
        key = mapping.get(name.name, name.name)
        if key in allowed_keys and isinstance(arg, SLiteral):
            gpu_info[key] = arg.value

    return gpu_info


def gpu_core(
    decorator: Decorator,
    fun_name: Name,
    typing_ctx: TypingContext,
    core_program: Term,
    metadata: Metadata,
) -> Metadata:
    _ = typing_ctx, core_program
    return metadata_update_by_name(metadata, fun_name, _gpu_options_from_decorator(decorator))
