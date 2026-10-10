from __future__ import annotations

from importlib.metadata import version
from dataclasses import dataclass, field
from pathlib import Path
from aeon.compilation.interface import (
    _module_export_name,
    _collect_trusted_names,
    _sugar_types_from_srec_chain,
    _exports_from_spine,
    _exports_from_uninterpreted,
    _add_inductive_member_export_aliases,
    _module_constructor_defs,
    _qualified_scope,
)

from aeon.compilation.link import (
    collect_dependency_units,
    link_compiled_units,
    link_rec_spines,
    link_typing_context,
)
from aeon.compilation.resolve import import_search_containers, resolve_import_path, resolve_module_source
from aeon.compilation.serialize import read_unit, source_hash, write_unit
from aeon.compilation.unit import AEC_FORMAT_VERSION, CompiledUnit
from aeon.compilation.session import SessionMapping, compilation_entrypoint, current_session
from aeon.core.bind import bind_ids, populate_mutual_companions
from aeon.core.terms import Literal, Term
from aeon.core.types import t_int, top
from aeon.decorators import Metadata, apply_core_decorators_phase
from aeon.elaboration import elaborate_collecting_errors
from aeon.errors import AeonError, ModuleNotFoundAeonError
from aeon.sugar.ast_helpers import st_top
from aeon.sugar.bind import bind, bind_program
from aeon.sugar.desugar import _bare_name, desugar
from aeon.sugar.instance_registry import clear_instance_registry
from aeon.sugar.lowering import lower_to_core, lower_to_core_context
from aeon.sugar.parser import parse_main_program
from aeon.sugar.program import ImportAe, Program
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type_errors
from aeon.utils.name import Name

_COMPILER_VERSION = version("AeonLang")


@dataclass
class CompilationState:
    sources: dict[str, CompiledUnit] = field(default_factory=dict)
    modules: dict[str, CompiledUnit] = field(default_factory=dict)


_source_cache = SessionMapping(lambda: current_session().state(CompilationState).sources)
_module_cache = SessionMapping(lambda: current_session().state(CompilationState).modules)


def clear_unit_cache() -> None:
    _source_cache.clear()
    _module_cache.clear()


def _resolve_module_source(module_path: str) -> str | None:
    """Resolve a module path (e.g. ``String``) to an absolute ``.ae`` file path."""
    return resolve_module_source(module_path)


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
        dep_unit, errors = compile_file(
            source, is_main=False, use_cache=True, write_cache=False, module_path=module_path
        )
        if errors:
            continue
        pending.extend(dep_unit.dependencies)


def _file_imports(program: Program) -> list[ImportAe]:
    inductive_names = {d.name.name for d in program.inductive_decls}
    return [imp for imp in program.imports if not (imp.is_open and imp.module_path in inductive_names)]


@compilation_entrypoint
def compile_file(
    filename: str,
    *,
    is_main: bool = False,
    is_main_hole: bool | None = None,
    use_cache: bool = True,
    write_cache: bool = True,
    module_path: str | None = None,
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
        module_path=module_path,
    )


@compilation_entrypoint
def compile_program(
    aeon_code: str,
    *,
    filename: str | None = None,
    is_main: bool = False,
    is_main_hole: bool | None = None,
    use_cache: bool = True,
    write_cache: bool = True,
    module_path: str | None = None,
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
            dep_errors.append(ModuleNotFoundAeonError(importel=imp, possible_containers=import_search_containers()))
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
        _unit, errors = compile_file(
            dep_path,
            is_main=False,
            use_cache=use_cache,
            write_cache=write_cache,
            module_path=imp.module_path,
        )
        dep_errors.extend(errors)

    if dep_errors:
        return _placeholder_unit(path, digest, dep_module_paths), dep_errors

    module_path = module_path or (Path(path).stem if path != "<stdin>" else "Main")
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

    dep_list = [dep_units[m] for m in dep_module_paths if m in dep_units]
    from aeon.backend.evaluator import HoleEvaluationError
    from aeon.errors import RefinementExecutionHoleError
    from aeon.utils.location import FileLocation
    from aeon.verification.refinement_exec import execute_refinements_in_sterm, sterm_has_user_hole

    _loc = FileLocation(path, (0, 0), (0, 0))
    if sterm_has_user_hole(sterm):
        if not is_main:
            return _placeholder_unit(path, digest, dep_module_paths), [
                RefinementExecutionHoleError(
                    "synthesis hole",
                    loc=_loc,
                )
            ]
    else:
        try:
            sterm = execute_refinements_in_sterm(sterm, dep_list)
        except HoleEvaluationError as e:
            return _placeholder_unit(path, digest, dep_module_paths), [RefinementExecutionHoleError(str(e), loc=_loc)]

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
    if export_prefix is not None:
        exports = _add_inductive_member_export_aliases(
            exports,
            desugared.local_inductive_decls,
            export_prefix,
        )
        private_exports = {
            _bare_name(export_prefix, definition.name.name) for definition in prog.definitions if definition.is_private
        }
        for bare in private_exports:
            exports.pop(bare, None)
        if prog.export_names:
            exports = {bare: export for bare, export in exports.items() if bare in set(prog.export_names)}
        for reexport_module, names in prog.reexports:
            dependency = dep_units.get(reexport_module)
            if dependency is None:
                continue
            for name in names:
                if name in exports:
                    raise ValueError(f"duplicate exported name '{name}'")
                export = dependency.exports.get(name)
                if export is None:
                    raise ValueError(f"cannot re-export '{name}' from '{reexport_module}'")
                exports[name] = export
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
        dep_unit, errors = compile_file(
            dep_path, is_main=False, use_cache=True, write_cache=False, module_path=imp.module_path
        )
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


@compilation_entrypoint
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


@compilation_entrypoint
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
