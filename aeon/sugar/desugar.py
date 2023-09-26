from __future__ import annotations

import os.path
from pathlib import Path

from aeon.backend.evaluator import EvaluationContext
from aeon.core.substitutions import substitute_vartype
from aeon.core.substitutions import substitute_vartype_in_term
from aeon.core.terms import Abstraction
from aeon.core.terms import Application
from aeon.core.terms import Hole
from aeon.core.terms import Literal
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import Var
from aeon.core.types import AbstractionType
from aeon.core.types import BaseType
from aeon.core.types import t_int
from aeon.prelude.prelude import evaluation_vars
from aeon.prelude.prelude import typing_vars
from aeon.sugar.parser import mk_parser
from aeon.sugar.program import Definition
from aeon.sugar.program import ImportAe
from aeon.sugar.program import Program
from aeon.sugar.program import TypeDecl
from aeon.typechecking.context import TypingContext
from aeon.typechecking.context import UninterpretedFunctionBinder
from aeon.utils.ctx_helpers import build_context


def desugar(p: Program) -> tuple[Term, TypingContext, EvaluationContext]:
    ctx = build_context(typing_vars)
    ectx = EvaluationContext(evaluation_vars)

    prog: Term
    if "main" in [d.name for d in p.definitions]:
        prog = Application(Var("main"), Literal(1, type=t_int))
    else:
        prog = Application(Var("print"), Hole("main"))

    defs: list[Definition] = p.definitions
    type_decls: list[TypeDecl] = p.type_decls
    imports: list[ImportAe] = p.imports

    imp: ImportAe
    for imp in imports:
        import_p: Program = handle_import(imp.path)

        defs = import_p.definitions + defs
        type_decls = import_p.type_decls + type_decls

    d: Definition
    for d in defs[::-1]:
        if d.body == Var("uninterpreted"):
            assert isinstance(d.type, AbstractionType)
            d_type = d.type
            for tyname in type_decls:
                d_type = substitute_vartype(d_type, BaseType(tyname.name),
                                            tyname.name)
            ctx += UninterpretedFunctionBinder(
                d.name,
                d_type,
            )
        else:
            ty = d.type
            body = d.body
            for a, t in d.args:
                ty = AbstractionType(a, t, ty)
                body = Abstraction(a, body)
            prog = Rec(d.name, ty, body, prog)

    tydeclname: TypeDecl
    for tydeclname in type_decls:
        prog = substitute_vartype_in_term(prog, BaseType(tydeclname.name),
                                          tydeclname.name)
    return (prog, ctx, ectx)


def handle_import(path: str) -> Program:
    """Imports a given path, following the precedence rules of current folder,
    AEONPATH."""
    possible_containers = ([Path.cwd()] + [Path.cwd() / "libraries"] + [
        Path(str) for str in os.environ.get("AEONPATH", ";").split(";") if str
    ])
    for container in possible_containers:
        file = container / f"{path}.ae"
        if file.exists():
            contents = open(file).read()
            return mk_parser("program").parse(contents)
    raise Exception(
        f"Could not import {path} in any of the following paths: " +
        ";".join([str(p) for p in possible_containers]), )
