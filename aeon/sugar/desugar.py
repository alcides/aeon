from __future__ import annotations

import os.path
from pathlib import Path

from aeon.backend.evaluator import EvaluationContext
from aeon.core.substitutions import substitute_vartype
from aeon.core.substitutions import substitute_vartype_in_term
from aeon.core.terms import Abstraction, Application
from aeon.core.terms import Hole
from aeon.core.terms import Literal
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import Var
from aeon.core.types import AbstractionType
from aeon.core.types import BaseType
from aeon.core.types import t_int
from aeon.decorators import apply_decorators, Metadata
from aeon.prelude.prelude import evaluation_vars
from aeon.prelude.prelude import typing_vars
from aeon.sugar.parser import mk_parser
from aeon.sugar.program import Definition
from aeon.sugar.program import ImportAe
from aeon.sugar.program import Program
from aeon.sugar.program import TypeDecl
from aeon.typechecking.context import TypingContext, UninterpretedFunctionBinder
from aeon.utils.ctx_helpers import build_context

ProgramComponents = tuple[Term, TypingContext, EvaluationContext, Metadata]


def desugar(p: Program) -> ProgramComponents:
    ctx, ectx = build_context(typing_vars), EvaluationContext(evaluation_vars)
    prog = determine_main_function(p)

    defs, type_decls = p.definitions, p.type_decls
    defs, type_decls = handle_imports(p.imports, defs, type_decls)
    defs, metadata = apply_decorators_in_definitions(defs)

    ctx, prog = update_program_and_context(prog, defs, ctx, type_decls)

    for tydeclname in type_decls:
        prog = substitute_vartype_in_term(prog, BaseType(tydeclname.name), tydeclname.name)

    return prog, ctx, ectx, metadata


def determine_main_function(p: Program) -> Term:
    if "main" in [d.name for d in p.definitions]:
        return Application(Var("main"), Literal(1, type=t_int))
    return Hole("main")


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
            import_p_definitions = [d for d in import_p_definitions if str(d.name) == imp.func]

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


def apply_decorators_in_definitions(definitions: list[Definition]) -> tuple[list[Definition], Metadata]:
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
    prog: Term,
    defs: list[Definition],
    ctx: TypingContext,
    type_decls: list[TypeDecl],
) -> tuple[TypingContext, Term]:

    for d in defs[::-1]:
        if d.body == Var("uninterpreted"):
            ctx = handle_uninterpreted(ctx, d, type_decls)
        else:
            prog = bind_program_to_rec(prog, d)
    return ctx, prog


def handle_uninterpreted(ctx: TypingContext, d: Definition, type_decls: list[TypeDecl]) -> TypingContext:
    assert isinstance(d.type, AbstractionType)
    d_type = d.type
    for tyname in type_decls:
        d_type = substitute_vartype(d_type, BaseType(tyname.name), tyname.name)
    return ctx + UninterpretedFunctionBinder(d.name, d_type)


def bind_program_to_rec(prog: Term, d: Definition) -> Term:
    ty, body = d.type, d.body
    for arg_name, arg_type in d.args[::-1]:
        ty = AbstractionType(arg_name, arg_type, ty)
        body = Abstraction(arg_name, body)
    return Rec(d.name, ty, body, prog)


def handle_import(path: str) -> Program:
    """Imports a given path, following the precedence rules of current folder,
    AEONPATH."""
    possible_containers = (
        [Path.cwd()] + [Path.cwd() / "libraries"] + [Path(s) for s in os.environ.get("AEONPATH", ";").split(";") if s]
    )
    for container in possible_containers:
        file = container / f"{path}"
        if file.exists():
            contents = open(file).read()
            return mk_parser("program").parse(contents)
    raise Exception(
        f"Could not import {path} in any of the following paths: " + ";".join([str(p) for p in possible_containers]),
    )
