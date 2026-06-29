from __future__ import annotations

import os
from importlib.metadata import version
from pathlib import Path

from aeon.compilation.link import (
    collect_dependency_units,
    link_compiled_units,
    link_rec_spines,
    link_typing_context,
)
from aeon.compilation.resolve import get_package_libraries_dir, resolve_import_path
from aeon.compilation.serialize import read_unit, source_hash, write_unit
from aeon.compilation.unit import AEC_FORMAT_VERSION, CompiledUnit, ModuleExport
from aeon.core.bind import bind_ids, populate_mutual_companions
from aeon.core.terms import Literal, Rec, Term
from aeon.core.types import Type, t_int, top
from aeon.decorators import Metadata, apply_core_decorators_phase
from aeon.elaboration import elaborate_collecting_errors
from aeon.facade.api import AeonError, ModuleNotFoundAeonError
from aeon.sugar.ast_helpers import st_top
from aeon.sugar.bind import bind, bind_program
from aeon.sugar.desugar import _bare_name, _is_native_import_def, desugar, type_of_definition
from aeon.sugar.instance_registry import clear_instance_registry
from aeon.sugar.lowering import lower_to_core, lower_to_core_context, type_to_core
from aeon.sugar.parser import parse_main_program
from aeon.sugar.program import ImportAe, Program, SRec, STerm
from aeon.sugar.program import Definition
from aeon.sugar.stypes import SType
from aeon.typechecking.context import TypingContext, UninterpretedBinder
from aeon.typechecking.typeinfer import check_type_errors
from aeon.utils.name import Name

_COMPILER_VERSION = version("AeonLang")

_source_cache: dict[str, CompiledUnit] = {}
_module_cache: dict[str, CompiledUnit] = {}


def clear_unit_cache() -> None:
    _source_cache.clear()
    _module_cache.clear()


def _resolve_module_source(module_path: str) -> str | None:
    """Resolve a module path (e.g. ``String``) to an absolute ``.ae`` file path."""
    rel = module_path.replace(".", "/") + ".ae"
    possible_containers = [Path.cwd(), Path.cwd() / "libraries"]
    pkg_libs = get_package_libraries_dir()
    if pkg_libs:
        possible_containers.append(pkg_libs)
    aeonpath = os.environ.get("AEONPATH", "")
    if aeonpath:
        possible_containers.extend(Path(s) for s in aeonpath.split(";") if s)
    for container in possible_containers:
        candidate = container / rel
        if candidate.exists():
            return str(candidate.resolve())
    return None


def _ensure_dependencies_cached(module_paths: list[str]) -> None:
    """Populate ``_module_cache`` with every transitive dependency unit."""
    pending = list(module_paths)
    seen: set[str] = set()
    while pending:
        module_path = pending.pop()
        if module_path in seen:
            continue
        seen.add(module_path)
        if module_path in _module_cache:
            pending.extend(_module_cache[module_path].dependencies)
            continue
        source = _resolve_module_source(module_path)
        if source is None:
            continue
        dep_unit, errors = compile_file(source, is_main=False, use_cache=True, write_cache=False)
        if errors:
            continue
        pending.extend(dep_unit.dependencies)


def _file_imports(program: Program) -> list[ImportAe]:
    inductive_names = {d.name.name for d in program.inductive_decls}
    return [imp for imp in program.imports if not (imp.is_open and imp.module_path in inductive_names)]


def _module_export_name(module_path: str) -> str:
    return module_path.split(".")[-1]


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
    definitions: list,
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
    for d in definitions:
        if export_prefix is not None:
            bare = _bare_name(export_prefix, d.name.name)
            internal_name = (
                d.name if d.name.name.startswith(f"{export_prefix}_") else Name(f"{export_prefix}_{bare}", d.name.id)
            )
        else:
            bare = d.name.name
            internal_name = d.name
        def_by_internal[internal_name.name] = d

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


def _module_constructor_defs(
    inductive_decls: list,
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
    qual = _module_export_name(module_path)
    return {(qual, bare): export.internal_name for bare, export in exports.items()}


def compile_file(
    filename: str,
    *,
    is_main: bool = False,
    is_main_hole: bool | None = None,
    use_cache: bool = True,
    write_cache: bool = True,
) -> tuple[CompiledUnit, list[AeonError]]:
    path = str(Path(filename).resolve())
    contents = Path(path).read_text(encoding="utf-8")
    return compile_program(
        contents,
        filename=path,
        is_main=is_main,
        is_main_hole=is_main_hole,
        use_cache=use_cache,
        write_cache=write_cache,
    )


def compile_program(
    aeon_code: str,
    *,
    filename: str | None = None,
    is_main: bool = False,
    is_main_hole: bool | None = None,
    use_cache: bool = True,
    write_cache: bool = True,
) -> tuple[CompiledUnit, list[AeonError]]:
    if filename is None:
        filename = "<stdin>"
    path = str(Path(filename).resolve()) if filename != "<stdin>" else filename
    digest = source_hash(aeon_code)
    # Main programs splice imported definitions during desugar; a cached spine
    # from an earlier compile would omit those bindings at runtime.
    cacheable = use_cache and not is_main and path != "<stdin>"

    if cacheable:
        cached = _source_cache.get(path) or read_unit(path)
        if (
            cached is not None
            and cached.source_hash == digest
            and cached.compiler_version == _COMPILER_VERSION
            and cached.format_version == AEC_FORMAT_VERSION
        ):
            _source_cache[path] = cached
            _module_cache[cached.module_path] = cached
            _ensure_dependencies_cached(cached.dependencies)
            return cached, []

    clear_instance_registry()
    prog = parse_main_program(aeon_code, filename=filename if filename != "<stdin>" else None)
    class_decls_snapshot = list(prog.class_decls)
    instance_decls_snapshot = list(prog.instance_decls)
    prog = bind_program(prog, [])

    file_imports = _file_imports(prog)
    dep_errors: list[AeonError] = []
    for imp in file_imports:
        if resolve_import_path(imp) is None:
            dep_errors.append(ModuleNotFoundAeonError(importel=imp, possible_containers=[Path.cwd()]))
    if dep_errors:
        return _placeholder_unit(path, digest, [imp.module_path for imp in file_imports]), dep_errors

    dep_units = compile_imports_for_desugar(file_imports)
    dep_module_paths = [imp.module_path for imp in file_imports]
    for imp in file_imports:
        if imp.module_path in dep_units:
            continue
        dep_path = resolve_import_path(imp)
        if dep_path is None:
            continue
        _unit, errors = compile_file(dep_path, is_main=False, use_cache=use_cache, write_cache=write_cache)
        dep_errors.extend(errors)

    if dep_errors:
        return _placeholder_unit(path, digest, dep_module_paths), dep_errors

    module_path = Path(path).stem if path != "<stdin>" else "Main"
    export_prefix = None if is_main else _module_export_name(module_path)
    main_hole = is_main if is_main_hole is None else is_main_hole

    try:
        desugared = desugar(
            prog,
            is_main_hole=main_hole,
            compiled_imports=dep_units,
            module_export_name=export_prefix,
        )
    except AeonError as e:
        return _placeholder_unit(path, digest, dep_module_paths), [e]

    elab_ctx, progt = bind(desugared.elabcontext, desugared.program)
    desugared = desugared._replace(elabcontext=elab_ctx, program=progt)

    export_sugar_types = _sugar_types_from_srec_chain(desugared.program)

    sterm, elab_errors = elaborate_collecting_errors(desugared.elabcontext, desugared.program, st_top)
    if elab_errors:
        return _placeholder_unit(path, digest, dep_module_paths), elab_errors

    typing_ctx = lower_to_core_context(desugared.elabcontext)
    core_ast = lower_to_core(sterm)
    typing_ctx, core_ast = bind_ids(typing_ctx, core_ast)
    core_ast = populate_mutual_companions(core_ast)

    # Main programs splice imported definitions during desugar; linking dependency
    # spines on top would duplicate binders and break name identity.
    if export_prefix is None:
        linked_core = core_ast
        linked_ctx = typing_ctx
    else:
        dep_list = [dep_units[m] for m in dep_module_paths if m in dep_units]
        linked_core = link_rec_spines(dep_list, core_ast) if dep_list else core_ast
        trusted = _collect_trusted_names(dep_list)
        linked_ctx = link_typing_context(dep_list, typing_ctx, trusted) if dep_list else typing_ctx

    # Library modules are typechecked when linked into a main program; checking
    # the grafted spine here rejects valid units whose internal names are
    # module-prefixed (e.g. ``Num_Ord_mk`` vs ``Ord_mk`` in instance dictionaries).
    type_errors: list[AeonError] = []
    if export_prefix is None:
        type_errors = list(check_type_errors(linked_ctx, linked_core, top))
    source_metadata: Metadata = dict(desugared.metadata)
    if type_errors and not is_main:
        return _placeholder_unit(path, digest, dep_module_paths), type_errors
    if type_errors:
        unit = CompiledUnit(
            format_version=AEC_FORMAT_VERSION,
            compiler_version=_COMPILER_VERSION,
            module_path=module_path,
            source_path=path,
            source_hash=digest,
            core_spine=linked_core,
            typing_ctx=linked_ctx,
            metadata=Metadata(),
            type_decls=list(prog.type_decls),
            inductive_decls=list(desugared.local_inductive_decls),
            class_decls=class_decls_snapshot,
            instance_decls=instance_decls_snapshot,
            constructor_to_type=dict(desugared.constructor_to_type),
            constructor_defs=dict(desugared.constructor_defs),
            exports={},
            qualified_scope={},
            dependencies=dep_module_paths,
            source_metadata=source_metadata,
        )
        return unit, type_errors

    exports = _exports_from_spine(core_ast, typing_ctx, prog.definitions, export_prefix, export_sugar_types)
    exports.update(_exports_from_uninterpreted(typing_ctx, export_prefix))

    metadata: Metadata = {}
    if is_main:
        metadata = apply_core_decorators_phase(linked_ctx, linked_core, desugared.metadata)

    unit = CompiledUnit(
        format_version=AEC_FORMAT_VERSION,
        compiler_version=_COMPILER_VERSION,
        module_path=module_path,
        source_path=path,
        source_hash=digest,
        core_spine=core_ast,
        typing_ctx=typing_ctx,
        metadata=metadata,
        type_decls=list(prog.type_decls),
        inductive_decls=list(desugared.local_inductive_decls),
        class_decls=class_decls_snapshot,
        instance_decls=instance_decls_snapshot,
        constructor_to_type=dict(desugared.constructor_to_type),
        constructor_defs=_module_constructor_defs(
            desugared.local_inductive_decls,
            desugared.constructor_defs,
            export_prefix,
        ),
        exports=exports,
        qualified_scope=_qualified_scope(exports, module_path) if export_prefix else {},
        dependencies=dep_module_paths,
        trusted_names=frozenset(v.internal_name for v in exports.values()),
        source_metadata=source_metadata,
    )

    if path != "<stdin>":
        _source_cache[path] = unit
        if export_prefix is not None:
            _module_cache[unit.module_path] = unit
        if write_cache and cacheable:
            write_unit(unit, path)

    return unit, []


def _placeholder_unit(path: str, digest: str, dependencies: list[str]) -> CompiledUnit:
    return CompiledUnit(
        format_version=AEC_FORMAT_VERSION,
        compiler_version=_COMPILER_VERSION,
        module_path=Path(path).stem if path != "<stdin>" else "Main",
        source_path=path,
        source_hash=digest,
        core_spine=Literal(0, t_int),
        typing_ctx=TypingContext(),
        metadata=Metadata(),
        type_decls=[],
        inductive_decls=[],
        class_decls=[],
        instance_decls=[],
        constructor_to_type={},
        constructor_defs={},
        exports={},
        qualified_scope={},
        dependencies=dependencies,
    )


def compile_imports_for_desugar(imports: list[ImportAe]) -> dict[str, CompiledUnit]:
    """Compile imported modules on demand for direct ``desugar`` callers."""
    units: dict[str, CompiledUnit] = {}
    pending = list(imports)
    seen: set[str] = set()
    while pending:
        imp = pending.pop()
        if imp.module_path in seen:
            continue
        seen.add(imp.module_path)
        if imp.module_path in units:
            pending.extend(ImportAe(module_path=dep) for dep in units[imp.module_path].dependencies)
            continue
        dep_path = resolve_import_path(imp)
        if dep_path is None:
            continue
        dep_unit, errors = compile_file(dep_path, is_main=False, use_cache=True, write_cache=False)
        if not errors:
            units[imp.module_path] = dep_unit
            pending.extend(ImportAe(module_path=dep) for dep in dep_unit.dependencies)
    return units


def dependency_units_for(unit: CompiledUnit) -> list[CompiledUnit]:
    _ensure_dependencies_cached(unit.dependencies)
    return collect_dependency_units(unit, _module_cache)


def _link_compiled_unit(
    unit: CompiledUnit,
    *,
    is_main: bool,
) -> tuple[Term, TypingContext, Metadata, frozenset[Name]]:
    if is_main:
        metadata: Metadata = {}
        if unit.source_metadata:
            metadata = apply_core_decorators_phase(unit.typing_ctx, unit.core_spine, dict(unit.source_metadata))
        return unit.core_spine, unit.typing_ctx, metadata, unit.trusted_names
    _ensure_dependencies_cached(unit.dependencies)
    dep_units = collect_dependency_units(unit, _module_cache)
    core, typing_ctx, metadata, trusted = link_compiled_units(unit, dep_units)
    return core, typing_ctx, metadata, trusted


def compile_and_link(
    filename: str,
    *,
    is_main: bool = True,
    is_main_hole: bool | None = None,
    use_cache: bool = True,
) -> tuple[CompiledUnit, Term | None, TypingContext | None, Metadata | None, frozenset[Name], list[AeonError]]:
    unit, errors = compile_file(filename, is_main=is_main, is_main_hole=is_main_hole, use_cache=use_cache)
    if errors:
        if is_main and unit.source_metadata:
            core, typing_ctx, metadata, trusted = _link_compiled_unit(unit, is_main=is_main)
            return unit, core, typing_ctx, metadata, trusted, errors
        return unit, None, None, None, frozenset(), errors
    core, typing_ctx, metadata, trusted = _link_compiled_unit(unit, is_main=is_main)
    return unit, core, typing_ctx, metadata, trusted, []


def compile_and_link_program(
    aeon_code: str,
    *,
    filename: str | None = None,
    is_main: bool = True,
    is_main_hole: bool | None = None,
    use_cache: bool = True,
) -> tuple[CompiledUnit, Term | None, TypingContext | None, Metadata | None, frozenset[Name], list[AeonError]]:
    unit, errors = compile_program(
        aeon_code,
        filename=filename,
        is_main=is_main,
        is_main_hole=is_main_hole,
        use_cache=use_cache,
        write_cache=filename is not None and filename != "<stdin>",
    )
    if errors:
        if is_main and unit.source_metadata:
            core, typing_ctx, metadata, trusted = _link_compiled_unit(unit, is_main=is_main)
            return unit, core, typing_ctx, metadata, trusted, errors
        return unit, None, None, None, frozenset(), errors
    core, typing_ctx, metadata, trusted = _link_compiled_unit(unit, is_main=is_main)
    return unit, core, typing_ctx, metadata, trusted, []
