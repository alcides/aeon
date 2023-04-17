from __future__ import annotations

import os.path

from aeon.backend.evaluator import EvaluationContext
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
from aeon.sugar.program import Namespace
from aeon.sugar.program import Program
from aeon.sugar.program import TypeDecl
from aeon.typechecking.context import TypingContext
from aeon.typechecking.context import VariableBinder
from aeon.utils.ctx_helpers import build_context


def flatten_namespace(n: Namespace | str) -> str:
    if isinstance(n, str):
        return n
    else:
        return f"{n.base}.{n.other}"


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
        name = flatten_namespace(d.name)
        if d.body == Var("uninterpreted"):
            ctx = VariableBinder(
                ctx,
                name,
                d.type,
            )  # TODO: ensure basic type in d.type
        else:
            ty = d.type
            body = d.body
            for a, t in d.args:
                ty = AbstractionType(a, t, ty)
                body = Abstraction(a, body)
            prog = Rec(name, ty, body, prog)

    tyname: TypeDecl
    for tyname in type_decls:
        prog = substitute_vartype_in_term(prog, BaseType(tyname.name), tyname.name)

    return (prog, ctx, ectx)


def handle_import(path: str) -> Program:
    filename = "libraries/" + path + ".ae"
    path = os.path.abspath(filename)
    assert os.path.exists(path), f"The library '{path}' does not exist. {path}"
    import_file_data = open(path).read()
    return mk_parser("program").parse(import_file_data)
