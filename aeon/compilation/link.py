from __future__ import annotations

from dataclasses import replace

from aeon.compilation.unit import CompiledUnit
from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    Hole,
    If,
    ImplicitRefinementHole,
    Let,
    Literal,
    Rec,
    RefinementAbstraction,
    RefinementApplication,
    Term,
    TypeAbstraction,
    TypeApplication,
    Var,
)
from aeon.decorators import Metadata
from aeon.elaboration.context import (
    ElabTypingContextEntry,
    ElaborationTypingContext,
)
from aeon.sugar.stypes import SType
from aeon.typechecking.context import TypingContext, TypingContextEntry
from aeon.utils.name import Name


def graft_spine(outer: Term, inner: Term) -> Term:
    """Replace the innermost body of ``outer``'s Rec chain with ``inner``."""
    match outer:
        case Rec() as rec:
            return replace(rec, body=graft_spine(rec.body, inner))
        case _:
            return inner


def _spine_binders(term: Term) -> dict[str, Name]:
    binders: dict[str, Name] = {}
    while isinstance(term, Rec):
        binders[term.var_name.name] = term.var_name
        term = term.body
    return binders


def _reconcile_names(term: Term, spine: dict[str, Name], bound: frozenset[str] = frozenset()) -> Term:
    """Align ``Var`` nodes with canonical ``Name`` ids on the linked ``Rec`` spine."""
    match term:
        case Var(name):
            if name.name in spine and name.name not in bound:
                canonical = spine[name.name]
                if canonical != name:
                    return Var(canonical)
            return term
        case Abstraction(var_name, body):
            return Abstraction(var_name, _reconcile_names(body, spine, bound | {var_name.name}))
        case Let(var_name, var_value, body, loc, multiplicity):
            return Let(
                var_name,
                _reconcile_names(var_value, spine, bound),
                _reconcile_names(body, spine, bound | {var_name.name}),
                loc=loc,
                multiplicity=multiplicity,
            )
        case Rec(var_name, var_type, var_value, body, decreasing_by, loc, multiplicity, mutual_group_id, companions):
            return Rec(
                var_name,
                var_type,
                _reconcile_names(var_value, spine, bound),
                _reconcile_names(body, spine, bound),
                decreasing_by=decreasing_by,
                loc=loc,
                multiplicity=multiplicity,
                mutual_group_id=mutual_group_id,
                companions=companions,
            )
        case Application(fun, arg):
            return Application(_reconcile_names(fun, spine, bound), _reconcile_names(arg, spine, bound))
        case If(cond, then, otherwise):
            return If(
                _reconcile_names(cond, spine, bound),
                _reconcile_names(then, spine, bound),
                _reconcile_names(otherwise, spine, bound),
            )
        case Annotation(expr, ty):
            return Annotation(_reconcile_names(expr, spine, bound), ty)
        case TypeApplication(body, ty):
            return TypeApplication(_reconcile_names(body, spine, bound), ty)
        case RefinementApplication(body, refinement):
            return RefinementApplication(_reconcile_names(body, spine, bound), refinement)
        case TypeAbstraction(name, kind, body):
            return TypeAbstraction(name, kind, _reconcile_names(body, spine, bound))
        case RefinementAbstraction(pname, sort, body):
            return RefinementAbstraction(pname, sort, _reconcile_names(body, spine, bound))
        case Literal() | Hole() | ImplicitRefinementHole():
            return term
        case _:
            return term


def reconcile_linked_names(term: Term) -> Term:
    spine = _spine_binders(term)
    if not spine:
        return term
    return _reconcile_names(term, spine)


def link_rec_spines(units_in_order: list[CompiledUnit], local_spine: Term) -> Term:
    """Nest dependency spines around a module's own spine.

    ``units_in_order`` lists dependencies outermost-first (from
    :func:`collect_dependency_units`). Grafting runs innermost-first so
    providers like ``Math`` end up outside consumers like ``Testing``.
    """
    result = local_spine
    for unit in reversed(units_in_order):
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


def link_typing_context(
    dependency_units: list[CompiledUnit], local_ctx: TypingContext, trusted: frozenset[Name]
) -> TypingContext:
    """Merge dependency contexts with local entries, dropping import duplicates."""
    dep_names: set[Name] = set()
    for unit in dependency_units:
        for export in unit.exports.values():
            dep_names.add(export.internal_name)
        dep_names.update(unit.trusted_names)

    local_entries = [e for e in local_ctx.entries if not (hasattr(e, "name") and getattr(e, "name") in dep_names)]
    return merge_typing_contexts(
        [u.typing_ctx for u in dependency_units] + [TypingContext(local_entries)],
        trusted=trusted,
    )


def merge_elab_contexts(contexts: list[ElaborationTypingContext]) -> ElaborationTypingContext:
    entries: list[ElabTypingContextEntry] = []
    constructor_to_type: dict[str, Name] = {}
    constructor_defs: dict[str, Name] = {}
    instances: list[tuple[Name, SType]] = []
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
    core = reconcile_linked_names(link_rec_spines(dependency_units, local_unit.core_spine))
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


def collect_constructor_names(unit: CompiledUnit, dependency_units: list[CompiledUnit]) -> set[str]:
    names: set[str] = set()
    for u in [unit, *dependency_units]:
        mod = u.module_path.split(".")[-1]
        for decl in u.inductive_decls:
            for cons in decl.constructors:
                bare = cons.name.name
                names.add(f"{decl.name.name}_{bare}")
                names.add(f"{mod}_{decl.name.name}_{bare}")
        names.update(n.name for n in u.constructor_defs.values())
    return names
