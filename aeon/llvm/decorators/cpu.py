from __future__ import annotations

from typing import Any

from aeon.core.terms import Term
from aeon.decorators.api import Metadata, metadata_update_by_name
from aeon.sugar.program import Decorator, SLiteral
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def _cpu_options_from_decorator(decorator: Decorator) -> dict[str, Any]:
    cpu_args: dict[str, Any] = {
        "cpu": True,
        "cpu_opt_level": 3,
        "cpu_log_ir": False,
        "cpu_debug": False,
        "cpu_cache": False,
    }

    arg_keys = ["cpu_opt_level", "cpu_log_ir", "cpu_debug", "cpu_cache"]

    for key, arg in zip(arg_keys, decorator.macro_args):
        if isinstance(arg, SLiteral):
            cpu_args[key] = arg.value

    mapping = {
        "opt_level": "cpu_opt_level",
        "log_ir": "cpu_log_ir",
        "debug": "cpu_debug",
        "cache": "cpu_cache",
    }
    for name, arg in decorator.named_args.items():
        key = mapping.get(name.name, name.name)
        if key in cpu_args and isinstance(arg, SLiteral):
            cpu_args[key] = arg.value
    return cpu_args


def cpu_core(
    decorator: Decorator,
    fun_name: Name,
    typing_ctx: TypingContext,
    core_program: Term,
    metadata: Metadata,
) -> Metadata:
    _ = typing_ctx, core_program
    return metadata_update_by_name(metadata, fun_name, _cpu_options_from_decorator(decorator))
