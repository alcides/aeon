from __future__ import annotations

from aeon.core.bind import bind_ids
from aeon.core.types import top
from aeon.elaboration import elaborate
from aeon.frontend.anf_converter import ensure_anf
from aeon.sugar.ast_helpers import st_top
from aeon.sugar.bind import bind, bind_program
from aeon.sugar.desugar import DesugaredProgram, desugar
from aeon.sugar.lowering import lower_to_core, lower_to_core_context
from aeon.sugar.parser import parse_main_program
from aeon.sugar.program import SVar
from aeon.decorators import apply_core_decorators_phase
from aeon.typechecking.typeinfer import check_type_errors


def test_parse_decreasing_by_on_definition():
    src = """
        def f (n:Int) : Int decreasing_by [n] = n;
        def main (_:Int) : Int = 0
    """
    p = parse_main_program(src, filename="<test>")
    p = bind_program(p, [])
    fdef = p.definitions[0]
    assert len(fdef.decreasing_by) == 1
    assert isinstance(fdef.decreasing_by[0], SVar)


def test_parse_decreasing_by_lex_list():
    src = """
        def g (m:Int)(n:Int) : Int decreasing_by [m, n] = m;
        def main (_:Int) : Int = 0
    """
    p = parse_main_program(src, filename="<test>")
    p = bind_program(p, [])
    gdef = p.definitions[0]
    assert len(gdef.decreasing_by) == 2
    assert isinstance(gdef.decreasing_by[0], SVar)
    assert isinstance(gdef.decreasing_by[1], SVar)


def test_factorial_nat_path_sensitive_terminates():
    src = """
        def fact (n:Int | n >= 0) : Int decreasing_by [n] =
          if n == 0 then 1 else n * fact (n - 1);
        def main (_:Int) : Int = fact 5
    """
    prog = parse_main_program(src, filename="<test>")
    prog = bind_program(prog, [])
    desugared = desugar(prog, is_main_hole=True)
    ctx, progt = bind(desugared.elabcontext, desugared.program)
    desugared = DesugaredProgram(
        progt, ctx, desugared.metadata, desugared.constructor_to_type, desugared.constructor_defs
    )
    sterm = elaborate(desugared.elabcontext, desugared.program, st_top)
    typing_ctx = lower_to_core_context(desugared.elabcontext)
    core_ast = lower_to_core(sterm)
    typing_ctx, core_ast = bind_ids(typing_ctx, core_ast)
    core_ast_anf = ensure_anf(core_ast)
    errors = list(check_type_errors(typing_ctx, core_ast_anf, top))
    assert errors == [], [type(e).__name__ for e in errors]
    apply_core_decorators_phase(typing_ctx, core_ast_anf, desugared.metadata)


def test_lexicographic_ackermann_typechecks():
    src = """
        def ack (m:Int | m >= 0)(n:Int | n >= 0) : Int decreasing_by [m, n] =
          if m == 0 then n + 1 else (if n == 0 then ack (m - 1) 1 else ack m (n - 1));
        def main (_:Int) : Int = ack 2 3
    """
    prog = parse_main_program(src, filename="<test>")
    prog = bind_program(prog, [])
    desugared = desugar(prog, is_main_hole=True)
    ctx, progt = bind(desugared.elabcontext, desugared.program)
    desugared = DesugaredProgram(
        progt, ctx, desugared.metadata, desugared.constructor_to_type, desugared.constructor_defs
    )
    sterm = elaborate(desugared.elabcontext, desugared.program, st_top)
    typing_ctx = lower_to_core_context(desugared.elabcontext)
    core_ast = lower_to_core(sterm)
    typing_ctx, core_ast = bind_ids(typing_ctx, core_ast)
    core_ast_anf = ensure_anf(core_ast)
    errors = list(check_type_errors(typing_ctx, core_ast_anf, top))
    assert errors == [], [type(e).__name__ for e in errors]
    apply_core_decorators_phase(typing_ctx, core_ast_anf, desugared.metadata)
