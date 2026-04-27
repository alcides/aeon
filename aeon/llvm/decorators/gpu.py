from __future__ import annotations

from typing import Any

from aeon.core.terms import Term
from aeon.decorators.api import Metadata, metadata_update_by_name
from aeon.sugar.program import Decorator, SLiteral
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def _gpu_options_from_decorator(decorator: Decorator) -> dict[str, Any]:
    gpu_info: dict[str, Any] = {
        "gpu": True,
        "gpu_device": "cuda",
        "gpu_target": "",
        "gpu_opt_level": 3,
        "gpu_log_ir": False,
        "gpu_debug": False,
        "gpu_cache": False,
        "gpu_block_size": 32,
        "gpu_thread_count": 128,
    }

    mapping = {
        "device": "gpu_device",
        "target": "gpu_target",
        "opt_level": "gpu_opt_level",
        "log_ir": "gpu_log_ir",
        "debug": "gpu_debug",
        "cache": "gpu_cache",
        "block_size": "gpu_block_size",
        "thread_count": "gpu_thread_count",
    }

    arg_keys = list(mapping.values())
    for key, arg in zip(arg_keys, decorator.macro_args):
        if isinstance(arg, SLiteral):
            gpu_info[key] = arg.value

    for name, arg in decorator.named_args.items():
        key = mapping.get(name.name, name.name)
        if key in gpu_info and isinstance(arg, SLiteral):
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
