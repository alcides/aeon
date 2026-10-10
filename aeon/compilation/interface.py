"""Pure construction of a compilation unit's public module interface."""

from __future__ import annotations

from aeon.compilation.unit import CompiledUnit, ModuleExport
from aeon.core.terms import Rec, Term
from aeon.core.types import Type
from aeon.sugar.desugar import _bare_name, _is_native_import_def, type_of_definition
from aeon.sugar.lowering import type_to_core
from aeon.sugar.program import Definition, InductiveDecl, SRec, STerm
from aeon.sugar.stypes import SType
from aeon.typechecking.context import TypingContext, UninterpretedBinder
from aeon.utils.name import Name


def _module_export_name(module_path: str) -> str:
    """Canonical internal prefix for a dotted source module path."""
    return module_path.replace(".", "_")


def _collect_trusted_names(units: list[CompiledUnit]) -> frozenset[Name]:
    names: set[Name] = set()
    for unit in units:
        names.update(export.internal_name for export in unit.exports.values())
    return frozenset(names)


def _sugar_types_from_srec_chain(prog: STerm) -> dict[str, SType]:
    types: dict[str, SType] = {}
    current = prog
    while isinstance(current, SRec):
        types[current.var_name.name] = current.var_type
        current = current.body
    return types


def _exports_from_spine(
    core_spine: Term,
    typing_ctx: TypingContext,
    definitions: list[Definition],
    export_prefix: str | None,
    export_sugar_types: dict[str, SType] | None = None,
) -> dict[str, ModuleExport]:
    rec_types: dict[str, Type] = {}
    spine_names: list[Name] = []
    spine = core_spine
    while isinstance(spine, Rec):
        rec_types[spine.var_name.name] = spine.var_type
        spine_names.append(spine.var_name)
        spine = spine.body

    def_by_internal: dict[str, Definition] = {}
    for definition in definitions:
        if export_prefix is not None:
            bare = _bare_name(export_prefix, definition.name.name)
            internal_name = (
                definition.name
                if definition.name.name.startswith(f"{export_prefix}_")
                else Name(f"{export_prefix}_{bare}", definition.name.id)
            )
        else:
            bare = definition.name.name
            internal_name = definition.name
        def_by_internal[internal_name.name] = definition

    exports: dict[str, ModuleExport] = {}
    for internal in spine_names:
        d = def_by_internal.get(internal.name)
        if d is not None and _is_native_import_def(d):
            bare = internal.name
        elif export_prefix is not None:
            bare = _bare_name(export_prefix, internal.name)
        else:
            bare = internal.name

        core_type: Type | None = rec_types.get(internal.name)
        if core_type is None:
            core_type = typing_ctx.type_of(internal)
        d = def_by_internal.get(internal.name)
        if core_type is None and d is not None:
            core_type = type_to_core(type_of_definition(d))

        sugar_type = (export_sugar_types or {}).get(internal.name)
        if sugar_type is None and d is not None:
            sugar_type = type_of_definition(d)
        if sugar_type is None and core_type is not None:
            from aeon.sugar.lifting import lift_type

            sugar_type = lift_type(core_type)

        if sugar_type is None or core_type is None:
            continue

        exports[bare] = ModuleExport(
            bare_name=bare,
            internal_name=internal,
            sugar_type=sugar_type,
            core_type=core_type,
        )
    return exports


def _exports_from_uninterpreted(
    typing_ctx: TypingContext,
    export_prefix: str | None,
) -> dict[str, ModuleExport]:
    """Export uninterpreted measures and projections that are not on the Rec spine."""
    from aeon.sugar.lifting import lift_type

    exports: dict[str, ModuleExport] = {}
    for entry in typing_ctx.entries:
        if not isinstance(entry, UninterpretedBinder):
            continue
        if export_prefix is not None:
            bare = _bare_name(export_prefix, entry.name.name)
        else:
            bare = entry.name.name
        exports[bare] = ModuleExport(
            bare_name=bare,
            internal_name=entry.name,
            sugar_type=lift_type(entry.type),
            core_type=entry.type,
        )
    return exports


def _add_inductive_member_export_aliases(
    exports: dict[str, ModuleExport],
    inductive_decls: list[InductiveDecl],
    export_prefix: str | None,
) -> dict[str, ModuleExport]:
    """Publish local ADT constructors and measures by their source names.

    Inductive lowering gives a constructor such as ``mk`` on ``Public`` an
    internal name like ``Interface_Public_mk``.  The generic spine exporter
    can only recover ``Public_mk`` from that name, which means an explicit
    ``export (mk)`` neither publishes nor re-exports the constructor.  Module
    interfaces use source-level names, so add aliases for the constructor and
    canonical measure member while retaining the same internal binder and
    type.  Ordinary definitions already arrive under their source names.
    """
    if export_prefix is None:
        return exports

    aliases = dict(exports)

    def alias(source_name: str, internal_name: str) -> None:
        member = next((export for export in exports.values() if export.internal_name.name == internal_name), None)
        if member is None:
            return
        # Do not silently choose between two identically named namespace
        # members.  Such a declaration remains addressable through its
        # datatype-qualified name, but cannot be exported as one bare module
        # member.
        existing = aliases.get(source_name)
        if existing is not None and existing.internal_name != member.internal_name:
            return
        aliases[source_name] = ModuleExport(source_name, member.internal_name, member.sugar_type, member.core_type)

    for decl in inductive_decls:
        for constructor in decl.constructors:
            alias(
                constructor.name.name,
                f"{export_prefix}_{decl.name.name}_{constructor.name.name}",
            )
        for measure in decl.measures:
            alias(
                measure.name.name,
                f"{export_prefix}_{decl.name.name}_{measure.name.name}",
            )
    return aliases


def _module_constructor_defs(
    inductive_decls: list[InductiveDecl],
    constructor_defs: dict[str, Name],
    export_prefix: str | None,
) -> dict[str, Name]:
    """Constructor map for this module's own inductives only (not imported copies)."""
    if export_prefix is None:
        return dict(constructor_defs)
    if not inductive_decls:
        return {}
    result: dict[str, Name] = {}
    for decl in inductive_decls:
        for cons in decl.constructors:
            bare = cons.name.name
            candidates = (
                f"{export_prefix}_{decl.name.name}_{bare}",
                f"{decl.name.name}_{bare}",
            )
            for candidate in candidates:
                match = next((v for v in constructor_defs.values() if v.name == candidate), None)
                if match is not None:
                    result[bare] = match
                    break
    return result


def _qualified_scope(exports: dict[str, ModuleExport], module_path: str) -> dict[tuple[str, str], Name]:
    return {(module_path, bare): export.internal_name for bare, export in exports.items()}
