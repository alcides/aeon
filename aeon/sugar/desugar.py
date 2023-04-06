from __future__ import annotations

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
from aeon.sugar.program import Definition
from aeon.sugar.program import TypeDecl
from aeon.sugar.program import Program
from aeon.sugar.program import ImportAe
from aeon.sugar.parser import mk_parser
from aeon.typechecking.context import TypingContext
from aeon.typechecking.context import VariableBinder
from aeon.utils.ctx_helpers import build_context

import os
import os.path

def desugar(p: Program) -> tuple[Term, TypingContext, EvaluationContext]:
    ctx = build_context(typing_vars)
    ectx = EvaluationContext(evaluation_vars)

    prog: Term
    if "main" in [d.name for d in p.definitions]:
        prog = Application(Var("main"), Literal(1, type=t_int))
    else:
        prog = Application(Var("print"), Hole("main"))
        
    defs: list[Definition] = p.definitions
    type_decls:list[TypeDecl] = p.type_decls
    
    import_defs, import_type_decls  = handle_imports(p)
    
    defs = import_defs + defs
    type_decls = import_type_decls + type_decls
    

    d: Definition
    for d in defs[::-1]:
        
        if d.body == Var("uninterpreted"):
            ctx = VariableBinder(
                ctx,
                d.name,
                d.type,
            )  # TODO: ensure basic type in d.type
        else:
            ty = d.type
            body = d.body
            for a, t in d.args:
                ty = AbstractionType(a, t, ty)
                body = Abstraction(a, body)
            prog = Rec(d.name, ty, body, prog)

    tyname:TypeDecl
    for tyname in type_decls:
        prog = substitute_vartype_in_term(prog, BaseType(tyname.name), tyname.name)

    return (prog, ctx, ectx)


def handle_imports(p: Program) -> tuple[list[Definition], list[TypeDecl]]:
    defs: list[Definition] = []
    type_decls: list[TypeDecl] = []

    imp: ImportAe
    for imp in p.imports:
        filename = f"libraries/{imp.path}.ae"
        path = os.path.abspath(filename)
        assert os.path.exists(path), f"The library '{path}' does not exist. {path}"
        
        imported_program = parse_import_file(path)
            
        import_defs, import_type_decls = handle_imports(imported_program)
            
        if imp.func_or_type:
            defs, type_decls = handle_function_imp(imp, imported_program, defs, type_decls, path)

        else:
            defs, type_decls = handle_regular_imp(imported_program, defs, type_decls)
            
        defs = import_defs + defs
        type_decls = import_type_decls + type_decls

        
    return defs , type_decls


def parse_import_file(path: str) -> Program:
    with open(path) as import_file_data:
        return mk_parser("program").parse(import_file_data.read())


def handle_function_imp(
    imp: ImportAe, 
    import_p: Program, 
    defs: list[Definition], 
    type_decls: list[TypeDecl] , 
    path: str
    ) -> tuple[list[Definition], list[TypeDecl]]:
    
    if any(str(defn.name) == imp.func_or_type for defn in import_p.definitions):
        defs += [elem for elem in import_p.definitions if str(
                elem.name) == imp.func_or_type]
        type_decls +=  import_p.type_decls
    elif any(str(typedec.name) == imp.func_or_type for typedec in import_p.type_decls):
        type_decls += [elem for elem in import_p.type_decls if str(
                elem.name) == imp.func_or_type]
    else:
        assert False, f"The function or type {imp.func_or_type} does not exist in {path}"

    return defs, type_decls

def handle_regular_imp(import_p: Program, defs: list[Definition], type_decls: list[TypeDecl]) -> tuple[list[Definition], list[TypeDecl]]:
    defs +=  import_p.definitions
    type_decls += import_p.type_decls
    return defs, type_decls
