import tempfile
from typing import Any

from aeon.compilation.compile import clear_unit_cache, compile_and_link_program
from aeon.core.bind import bind_ctx, bind_ids, bind_term, bind_type
from aeon.core.parser import parse_term
from aeon.core.terms import Term
from aeon.core.types import Type, top
from aeon.elaboration import elaborate
from aeon.elaboration.context import build_typing_context
from aeon.facade.api import AeonError
from aeon.prelude.prelude import evaluation_vars, typing_vars
from aeon.sugar.desugar import desugar
from aeon.sugar.lowering import lower_to_core, lower_to_core_context, type_to_core
from aeon.sugar.parser import parse_expression, parse_program
from aeon.sugar.program import STerm
from aeon.sugar.stypes import SType
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type, check_type_errors
from aeon.backend.evaluator import EvaluationContext, eval
from aeon.decorators import Metadata, apply_core_decorators_phase
from aeon.utils.name import Name


def _compile_source(source: str, *, is_main_hole: bool = True) -> tuple[Term, TypingContext, Metadata] | None:
    clear_unit_cache()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".ae", delete=False, encoding="utf-8") as tmp:
        tmp.write(source)
        path = tmp.name
    _unit, core, typing_ctx, metadata, _trusted, errors = compile_and_link_program(
        source,
        filename=path,
        is_main=True,
        is_main_hole=is_main_hole,
    )
    if errors or core is None or typing_ctx is None or metadata is None:
        return None
    return core, typing_ctx, metadata


def check_compile(source: str, ty: SType, val=None, extra_vars=None) -> bool:
    if extra_vars:
        ectx = EvaluationContext(evaluation_vars)
        prog = parse_program(source)
        desugared = desugar(prog, extra_vars)
        try:
            sterm = elaborate(desugared.elabcontext, desugared.program)
        except AeonError:
            return False
        core_ast = lower_to_core(sterm)
        typing_ctx = lower_to_core_context(desugared.elabcontext)
        typing_ctx, core_ast = bind_ids(typing_ctx, core_ast)
    else:
        compiled = _compile_source(source)
        if compiled is None:
            return False
        core_ast, typing_ctx, metadata = compiled
        apply_core_decorators_phase(typing_ctx, core_ast, metadata)
        ectx = EvaluationContext(evaluation_vars, metadata=metadata)

    ty_core = type_to_core(ty)
    if not check_type(typing_ctx, core_ast, ty_core):
        return False

    if val is not None:
        r = eval(core_ast, ectx)
        assert r == val
    return True


def check_compile_expr(source: str, ty: SType, val: Any = None, extra_vars: dict[Name, SType] | None = None) -> bool:
    ectx = EvaluationContext(evaluation_vars)
    vs = {} if extra_vars is None else extra_vars
    vs.update(typing_vars)
    elabcontext = build_typing_context(vs)
    expr = parse_expression(source)
    try:
        sterm: STerm = elaborate(elabcontext, expr, ty)
    except AeonError:
        return False
    core_ast = lower_to_core(sterm)
    typing_ctx = lower_to_core_context(elabcontext)

    # Bind everything, so we also bind type at the same type:
    typing_ctx, subs = bind_ctx(typing_ctx, [])
    core_ast = bind_term(core_ast, subs)
    core_ty = bind_type(type_to_core(ty), subs)

    if not check_type(typing_ctx, core_ast, core_ty):
        return False

    if val is None:
        return True
    r = eval(core_ast, ectx)
    return r == val


def check_compile_core(source: str, ty: Type, val: Any = None):
    ectx = EvaluationContext(evaluation_vars)
    elabcontext = build_typing_context(typing_vars)
    typing_ctx = lower_to_core_context(elabcontext)

    core_ast = parse_term(source)
    typing_ctx, core_ast = bind_ids(typing_ctx, core_ast)
    assert check_type(typing_ctx, core_ast, ty)

    if val is not None:
        r = eval(core_ast, ectx)
        assert r == val


def extract_core(source: str) -> Term:
    compiled = _compile_source(source)
    if compiled is not None:
        core_ast, typing_ctx, metadata = compiled
        apply_core_decorators_phase(typing_ctx, core_ast, metadata)
        return core_ast

    prog = parse_program(source)
    desugared = desugar(prog)
    sterm = elaborate(desugared.elabcontext, desugared.program)
    core_ast = lower_to_core(sterm)
    typing_ctx = lower_to_core_context(desugared.elabcontext)
    typing_ctx, core_ast = bind_ids(typing_ctx, core_ast)
    if not list(check_type_errors(typing_ctx, core_ast, top)):
        apply_core_decorators_phase(typing_ctx, core_ast, desugared.metadata)
    return core_ast


def check_and_return_core(source) -> tuple[Term, TypingContext, EvaluationContext, Metadata]:
    compiled = _compile_source(source)
    ectx = EvaluationContext(evaluation_vars)
    if compiled is not None:
        core_ast, typing_ctx, metadata = compiled
        metadata = apply_core_decorators_phase(typing_ctx, core_ast, metadata)
        ectx = EvaluationContext(evaluation_vars, metadata=metadata)
        assert check_type(typing_ctx, core_ast, top)
        return core_ast, typing_ctx, ectx, metadata

    prog = parse_program(source)
    desugared = desugar(prog)
    sterm = elaborate(desugared.elabcontext, desugared.program)
    core_ast = lower_to_core(sterm)
    ctx = lower_to_core_context(desugared.elabcontext)
    typing_ctx, core_ast = bind_ids(ctx, core_ast)
    assert check_type(typing_ctx, core_ast, top)
    metadata = apply_core_decorators_phase(typing_ctx, core_ast, desugared.metadata)
    return core_ast, typing_ctx, ectx, metadata
