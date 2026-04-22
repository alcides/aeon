"""A decorator represents the modification of the program around a function.

There are two *registration* phases (usage syntax is always ``@name(...)``):

- **Sugar** (default): runs on the surface ``Definition`` during desugaring,
  before elaboration and typechecking.
- **Core**: runs after lowering to core, ANF conversion, and typechecking; see
  ``aeon.synthesis.core_decorators`` (registry ``core_decorators_environment``) and
  ``apply_core_decorators_phase``.
"""

from __future__ import annotations

from dataclasses import replace

from aeon.core.terms import Term
from aeon.decorators.api import CORE_DECORATOR_QUEUE_META_KEY, DecoratorType, Metadata
from aeon.llvm.decorators.gpu import gpu
from aeon.llvm.decorators.llvm import llvm
from aeon.sugar.program import Decorator, Definition
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
    minimize_float,
    minimize_int,
    multi_minimize_float,
    prompt,
)
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name

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
}

# Backwards-compatible name (sugar-phase registry only).
decorators_environment: dict[str, DecoratorType] = sugar_decorators_environment


def apply_decorators(fun: Definition, metadata: Metadata) -> tuple[Definition, list[Definition], Metadata]:
    """Apply sugar-phase decorators only; core-phase decorators stay on ``fun.decorators``."""
    if not metadata:
        metadata = {}
    sugar_decs: list[Decorator] = []
    core_decs: list[Decorator] = []
    for decorator in fun.decorators:
        dname = decorator.name.name
        if dname in sugar_decorators_environment:
            sugar_decs.append(decorator)
        elif dname in core_decorators_environment:
            core_decs.append(decorator)
        else:
            raise Exception(f"Unknown decorator named {dname}, in function {fun.name}.")

    partial = replace(fun, decorators=core_decs)
    total_extra: list[Definition] = []
    for decorator in sugar_decs:
        dname = decorator.name.name
        decorator_processor = sugar_decorators_environment[dname]
        partial, extra, metadata = decorator_processor(decorator, partial, metadata)
        total_extra.extend(extra)
    return partial, total_extra, metadata


def collect_core_decorator_queue(
    definitions: list[Definition], metadata: Metadata
) -> tuple[list[Definition], Metadata]:
    """Move core-phase decorators from definitions into ``metadata`` for later execution."""
    queue: list[tuple[Name, Decorator]] = list(metadata.get(CORE_DECORATOR_QUEUE_META_KEY, []) or [])
    new_definitions: list[Definition] = []
    for d in definitions:
        match d:
            case Definition(name, foralls, args, rtype, body, decorators, rforalls, decreasing_by, loc):
                for dec in decorators:
                    if dec.name.name not in core_decorators_environment:
                        raise ValueError(
                            f"Unexpected decorator {dec.name.name!r} on function {name.name!r} "
                            "(expected only core-phase decorators at this stage)."
                        )
                    queue.append((name, dec))
                new_definitions.append(
                    Definition(
                        name,
                        foralls,
                        args,
                        rtype,
                        body,
                        [],
                        rforalls,
                        decreasing_by,
                        loc,
                    )
                )
            case _:
                raise AssertionError(d)
    md = dict(metadata)
    md[CORE_DECORATOR_QUEUE_META_KEY] = queue
    return new_definitions, md


def apply_core_decorators_phase(
    typing_ctx: TypingContext,
    core_program: Term,
    metadata: Metadata,
) -> Metadata:
    """Run decorators registered in ``core_decorators_environment`` (after typechecking)."""
    queue_obj = metadata.pop(CORE_DECORATOR_QUEUE_META_KEY, None)
    queue: list[tuple[Name, Decorator]] = list(queue_obj or [])
    if not queue:
        return metadata
    md: Metadata = metadata
    for fname, dec in queue:
        dname = dec.name.name
        proc = core_decorators_environment[dname]
        md = proc(dec, fname, typing_ctx, core_program, md)
    return md
