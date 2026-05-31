"""Decorator dispatching infrastructure. The orchestration —
``apply_decorators`` (sugar phase), ``collect_core_decorator_queue``
(stash core decorators on metadata), ``apply_core_decorators_phase``
(run them after typechecking) — lives in Rust now
(``aeon-rs/src/decorators.rs``). The two registries below (``sugar_``
and ``core_decorators_environment``) and the decorator function bodies
they point to remain Python; Rust looks them up via FFI at dispatch
time.
"""

from __future__ import annotations

from aeon.decorators.api import CORE_DECORATOR_QUEUE_META_KEY, DecoratorType, Metadata
from aeon.synthesis.core_decorators import core_decorators_environment
from aeon.synthesis.decorators import (
    allow_recursion,
    csv_data,
    csv_file,
    disable_control_flow,
    error_fitness,
    hide,
    hide_types,
    maximize,
    maximize_float,
    maximize_int,
    minimize,
    minimize_cputime,
    minimize_energy,
    minimize_float,
    minimize_int,
    multi_minimize_float,
    prompt,
)

from aeon_rs import (
    apply_core_decorators_phase,
    apply_decorators,
    collect_core_decorator_queue,
)

sugar_decorators_environment: dict[str, DecoratorType] = {
    "minimize_int": minimize_int,
    "maximize_int": maximize_int,
    "minimize_float": minimize_float,
    "maximize_float": maximize_float,
    "multi_minimize_float": multi_minimize_float,
    "hide": hide,
    "hide_types": hide_types,
    "allow_recursion": allow_recursion,
    "error_fitness": error_fitness,
    "disable_control_flow": disable_control_flow,
    "prompt": prompt,
    "csv_data": csv_data,
    "csv_file": csv_file,
    "minimize": minimize,
    "maximize": maximize,
    "minimize_cputime": minimize_cputime,
    "minimize_energy": minimize_energy,
}

# Backwards-compatible alias.
decorators_environment: dict[str, DecoratorType] = sugar_decorators_environment

__all__ = [
    "CORE_DECORATOR_QUEUE_META_KEY",
    "DecoratorType",
    "Metadata",
    "apply_core_decorators_phase",
    "apply_decorators",
    "collect_core_decorator_queue",
    "core_decorators_environment",
    "decorators_environment",
    "sugar_decorators_environment",
]
