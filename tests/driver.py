from typing import Any
from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.elaboration.context import build_typing_context
from aeon.prelude.prelude import evaluation_vars
from aeon.prelude.prelude import typing_vars
from aeon.sugar.desugar import desugar
from aeon.sugar.lowering import lower_to_core, lower_to_core_context, type_to_core
from aeon.sugar.parser import parse_program
from aeon.sugar.parser import parse_expression
from aeon.sugar.program import STerm
from aeon.sugar.stypes import SType
from aeon.elaboration import elaborate
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type
from aeon.backend.evaluator import EvaluationContext
from aeon.backend.evaluator import eval
from aeon.decorators import Metadata

from aeon.frontend.parser import parse_term
from aeon.core.types import top

from aeon.frontend.anf_converter import ensure_anf


def check_compile(source: str, ty: SType, val=None, extra_vars=None):
    ectx = EvaluationContext(evaluation_vars)
    prog = parse_program(source)
    desugared = desugar(prog, extra_vars)
    sterm = elaborate(desugared.elabcontext, desugared.program)
    core_ast = lower_to_core(sterm)
    typing_ctx = lower_to_core_context(desugared.elabcontext)

    core_ast_anf = ensure_anf(core_ast)
    assert check_type(typing_ctx, core_ast_anf, type_to_core(ty))

    if val:
        r = eval(core_ast_anf, ectx)
        assert r == val


def check_compile_expr(source: str,
                       ty: SType,
                       val: Any = None,
                       extra_vars=None):
    ectx = EvaluationContext(evaluation_vars)
    vs = {} if extra_vars is None else extra_vars
    vs.update(typing_vars)
    elabcontext = build_typing_context(vs)
    expr = parse_expression(source)
    sterm: STerm = elaborate(elabcontext, expr, ty)
    core_ast = lower_to_core(sterm)
    typing_ctx = lower_to_core_context(elabcontext)

    core_ast_anf = ensure_anf(core_ast)
    assert check_type(typing_ctx, core_ast_anf, type_to_core(ty))

    if val is not None:
        r = eval(core_ast_anf, ectx)
        assert r == val


def check_compile_core(source: str, ty: Type, val: Any = None):
    ectx = EvaluationContext(evaluation_vars)
    elabcontext = build_typing_context(typing_vars)
    typing_ctx = lower_to_core_context(elabcontext)

    core_ast = parse_term(source)
    core_ast_anf = ensure_anf(core_ast)
    assert check_type(typing_ctx, core_ast_anf, ty)

    if val is not None:
        r = eval(core_ast_anf, ectx)
        assert r == val


def extract_core(source: str) -> Term:
    prog = parse_program(source)
    desugared = desugar(prog)
    sterm = elaborate(desugared.elabcontext, desugared.program)
    core_ast = lower_to_core(sterm)

    core_ast_anf = ensure_anf(core_ast)
    return core_ast_anf


def check_and_return_core(
        source) -> tuple[Term, TypingContext, EvaluationContext, Metadata]:
    ectx = EvaluationContext(evaluation_vars)
    prog = parse_program(source)
    desugared = desugar(prog)
    sterm = elaborate(desugared.elabcontext, desugared.program)
    core_ast = lower_to_core(sterm)
    ctx = lower_to_core_context(desugared.elabcontext)

    core_ast_anf = ensure_anf(core_ast)
    assert check_type(ctx, core_ast_anf, top)
    return core_ast_anf, ctx, ectx, desugared.metadata
