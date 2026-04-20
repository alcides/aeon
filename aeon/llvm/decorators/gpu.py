from __future__ import annotations

from typing import Any

from aeon.decorators.api import Metadata, metadata_update
from aeon.sugar.program import Definition, SLiteral, Decorator


def gpu(
    decorator: Decorator,
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    gpu_info: dict[str, Any] = {
        "gpu": True,
        "gpu_device": "cuda",
        "gpu_debug": False,
        "gpu_cache": False,
        "gpu_block_size": 1,
        "gpu_thread_count": 1,
    }

    arg_keys = ["gpu_device", "gpu_debug", "gpu_cache", "gpu_block_size", "gpu_thread_count"]

    for key, arg in zip(arg_keys, decorator.macro_args):
        if isinstance(arg, SLiteral):
            gpu_info[key] = arg.value

    mapping = {
        "target": "gpu_device",
        "device": "gpu_device",
        "debug": "gpu_debug",
        "cache": "gpu_cache",
        "block_size": "gpu_block_size",
        "thread_count": "gpu_thread_count",
    }
    for name, arg in decorator.named_args.items():
        key = mapping.get(name.name, name.name)
        if key in gpu_info and isinstance(arg, SLiteral):
            gpu_info[key] = arg.value

    metadata = metadata_update(metadata, fun, gpu_info)
    return fun, [], metadata
