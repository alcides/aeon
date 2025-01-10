from __future__ import annotations

import os.path
from pathlib import Path
from typing import NamedTuple

from aeon.decorators import apply_decorators, Metadata
from aeon.elaboration.context import (
    ElabUninterpretedBinder,
    ElabVariableBinder,
    ElaborationTypingContext,
    TypingContextEntry,
    build_typing_context,
)
from aeon.prelude.prelude import typing_vars
from aeon.sugar.parser import mk_parser
from aeon.sugar.program import Definition, SAbstraction, SApplication, SHole, SLiteral, SRec, STerm, SVar
from aeon.sugar.program import ImportAe
from aeon.sugar.program import Program
from aeon.sugar.program import TypeDecl
from aeon.sugar.stypes import SAbstractionType, SBaseType, SType, builtin_types
from aeon.sugar.substitutions import substitute_svartype_in_stype, substitution_svartype_in_sterm


class DesugaredProgram(NamedTuple):
    program: STerm
    elabcontext: ElaborationTypingContext
    metadata: Metadata


def desugar(p: Program,
            extra_vars: dict[str, SType] | None = None) -> DesugaredProgram:

    vs = {} if extra_vars is None else extra_vars
    vs.update(typing_vars)
    etctx = build_typing_context(vs)
    prog = determine_main_function(p)

    defs, type_decls = p.definitions, p.type_decls
    defs, type_decls = handle_imports(p.imports, defs, type_decls)
    defs, metadata = apply_decorators_in_definitions(defs)

    etctx, prog = update_program_and_context(prog, defs, etctx)

    prog, etctx = replace_concrete_types(
        prog, etctx, builtin_types + [td.name for td in type_decls])

    return DesugaredProgram(prog, etctx, metadata)


def determine_main_function(p: Program) -> STerm:
    if "main" in [d.name for d in p.definitions]:
        return SApplication(SVar("main"), SLiteral(1, type=SBaseType("Int")))
    return SHole("main")


def handle_imports(
    imports: list[ImportAe],
    defs: list[Definition],
    type_decls: list[TypeDecl],
) -> tuple[list[Definition], list[TypeDecl]]:
    for imp in imports[::-1]:
        import_p = handle_import(imp.path)
        import_p_definitions = import_p.definitions
        defs_recursive: list[Definition] = []
        type_decls_recursive: list[TypeDecl] = []
        if import_p.imports:
            defs_recursive, type_decls_recursive = handle_imports(
                import_p.imports,
                import_p.definitions,
                import_p.type_decls,
            )
        if imp.func:
            import_p_definitions = [
                d for d in import_p_definitions if str(d.name) == imp.func
            ]

        defs = defs_recursive + import_p_definitions + defs
        type_decls = type_decls_recursive + import_p.type_decls + type_decls
    return defs, type_decls


def apply_decorators_in_program(prog: Program) -> Program:
    """We apply the decorators meta-programming code to each definition in the
    program."""
    defs, _ = apply_decorators_in_definitions(prog.definitions)
    return Program(
        imports=prog.imports,
        type_decls=prog.type_decls,
        definitions=defs,
    )


def apply_decorators_in_definitions(
        definitions: list[Definition]) -> tuple[list[Definition], Metadata]:
    """We apply the decorators meta-programming code to each definition in the
    program."""
    metadata: Metadata = {}
    new_definitions = []
    for definition in definitions:
        new_def, other_defs, metadata = apply_decorators(definition, metadata)
        new_definitions.append(new_def)
        new_definitions.extend(other_defs)
    return new_definitions, metadata


def update_program_and_context(
    prog: STerm,
    defs: list[Definition],
    ctx: ElaborationTypingContext,
) -> tuple[ElaborationTypingContext, STerm]:
    for d in defs[::-1]:
        if d.body == SVar("uninterpreted"):
            ctx.entries.append(ElabUninterpretedBinder(d.name, d.type))
        else:
            prog = convert_definition_to_srec(prog, d)
    return ctx, prog


def replace_concrete_types(
        t: STerm, etctx: ElaborationTypingContext,
        types: list[str]) -> tuple[STerm, ElaborationTypingContext]:
    """Replaces all occurrences of STypeVar with the corresponding SBaseType."""
    for name in types:
        t = substitution_svartype_in_sterm(t, SBaseType(name), name)

    def fix_vartype(e: TypingContextEntry) -> TypingContextEntry:
        match e:
            case ElabVariableBinder(vname, ty):
                nty = ty
                for name in types:
                    nty = substitute_svartype_in_stype(nty, SBaseType(name),
                                                       name)
                return ElabVariableBinder(vname, nty)
            case ElabUninterpretedBinder(vname, ty):
                nty = ty
                for name in types:
                    nty = substitute_svartype_in_stype(nty, SBaseType(name),
                                                       name)
                return ElabUninterpretedBinder(vname, nty)
            case _:
                return e

    return t, ElaborationTypingContext([fix_vartype(e) for e in etctx.entries])


def convert_definition_to_srec(prog: STerm, d: Definition) -> STerm:
    ty, body = d.type, d.body
    for arg_name, arg_type in d.args[::-1]:
        ty = SAbstractionType(arg_name, arg_type, ty)
        body = SAbstraction(arg_name, body)
    return SRec(d.name, ty, body, prog)


def handle_import(path: str) -> Program:
    """Imports a given path, following the precedence rules of current folder,
    AEONPATH."""
    possible_containers = (
        [Path.cwd()] + [Path.cwd() / "libraries"] +
        [Path(s) for s in os.environ.get("AEONPATH", ";").split(";") if s])
    for container in possible_containers:
        file = container / f"{path}"
        if file.exists():
            contents = open(file).read()
            return mk_parser("program").parse(contents)
    raise Exception(
        f"Could not import {path} in any of the following paths: " +
        ";".join([str(p) for p in possible_containers]), )
