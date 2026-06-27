from __future__ import annotations

from dataclasses import replace

from aeon.compilation.unit import CompiledUnit
from aeon.core.terms import Rec, Term
from aeon.decorators import Metadata
from aeon.elaboration.context import (
    ElabTypingContextEntry,
    ElaborationTypingContext,
)
from aeon.typechecking.context import TypingContext, TypingContextEntry
from aeon.utils.name import Name


def graft_spine(outer: Term, inner: Term) -> Term:
    """Replace the innermost body of ``outer``'s Rec chain with ``inner``."""
    match outer:
        case Rec() as rec:
            return replace(rec, body=graft_spine(rec.body, inner))
        case _:
            return inner


def link_rec_spines(units_in_order: list[CompiledUnit], local_spine: Term) -> Term:
    """Nest dependency spines around a module's own spine.

    ``units_in_order`` lists dependencies outermost-first (same order as
    ``handle_imports`` prepends definitions).
    """
    result = local_spine
    for unit in units_in_order:
        result = graft_spine(unit.core_spine, result)
    return result


def merge_typing_contexts(contexts: list[TypingContext], trusted: frozenset[Name] | None = None) -> TypingContext:
    entries: list[TypingContextEntry] = []
    seen: set[TypingContextEntry] = set()
    trusted_names: set[Name] = set(trusted or ())
    for ctx in contexts:
        trusted_names.update(ctx.trusted_names)
        for entry in ctx.entries:
            if entry not in seen:
                entries.append(entry)
                seen.add(entry)
    return TypingContext(entries, trusted_names=frozenset(trusted_names))


def link_typing_context(dependency_units: list[CompiledUnit], local_ctx: TypingContext, trusted: frozenset[Name]) -> TypingContext:
    """Merge dependency contexts with local entries, dropping import duplicates."""
    dep_names: set[Name] = set()
    for unit in dependency_units:
        for export in unit.exports.values():
            dep_names.add(export.internal_name)
        dep_names.update(unit.trusted_names)

    local_entries = [
        e
        for e in local_ctx.entries
        if not (hasattr(e, "name") and getattr(e, "name") in dep_names)
    ]
    return merge_typing_contexts(
        [u.typing_ctx for u in dependency_units] + [TypingContext(local_entries)],
        trusted=trusted,
    )


def merge_elab_contexts(contexts: list[ElaborationTypingContext]) -> ElaborationTypingContext:
    entries: list[ElabTypingContextEntry] = []
    constructor_to_type: dict[str, Name] = {}
    constructor_defs: dict[str, Name] = {}
    instances: list[tuple[Name, object]] = []
    for ctx in contexts:
        entries.extend(ctx.entries)
        constructor_to_type.update(ctx.constructor_to_type)
        constructor_defs.update(ctx.constructor_defs)
        instances.extend(ctx.instances)
    return ElaborationTypingContext(entries, constructor_to_type, constructor_defs, instances)


def merge_metadata(parts: list[Metadata]) -> Metadata:
    merged: Metadata = {}
    for part in parts:
        merged.update(part)
    return merged


def link_compiled_units(
    local_unit: CompiledUnit,
    dependency_units: list[CompiledUnit],
) -> tuple[Term, TypingContext, Metadata, frozenset[Name]]:
    """Link a module with its dependencies into a runnable core program."""
    core = link_rec_spines(dependency_units, local_unit.core_spine)
    trusted = frozenset().union(*(u.trusted_names for u in dependency_units))
    typing_ctx = link_typing_context(dependency_units, local_unit.typing_ctx, trusted)
    metadata = merge_metadata([u.metadata for u in dependency_units] + [local_unit.metadata])
    return core, typing_ctx, metadata, trusted


def collect_dependency_units(
    unit: CompiledUnit,
    cache: dict[str, CompiledUnit],
) -> list[CompiledUnit]:
    """Return dependency units in link order (outermost first)."""
    ordered: list[CompiledUnit] = []
    seen: set[str] = set()

    def visit(dep_path: str) -> None:
        if dep_path in seen:
            return
        seen.add(dep_path)
        dep = cache.get(dep_path)
        if dep is None:
            return
        for sub in dep.dependencies:
            visit(sub)
        ordered.append(dep)

    for dep_path in unit.dependencies:
        visit(dep_path)
    return ordered
