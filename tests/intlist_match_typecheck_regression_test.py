from __future__ import annotations

from pathlib import Path

from aeon.core.bind import bind_ids
from aeon.core.types import top
from aeon.elaboration import elaborate
from aeon.frontend.anf_converter import ensure_anf
from aeon.sugar.ast_helpers import st_top
from aeon.sugar.bind import bind, bind_program
from aeon.sugar.desugar import DesugaredProgram, desugar
from aeon.sugar.lowering import lower_to_core, lower_to_core_context
from aeon.sugar.parser import parse_main_program
from aeon.typechecking.typeinfer import check_type_errors


def test_intlist_len_match_typechecks() -> None:
    """Verifies that ``tests/fixtures/intlist_len_match.ae`` typechecks after ANF keeps lambdas inline."""
    path = Path(__file__).resolve().parent / "fixtures" / "intlist_len_match.ae"
    src = path.read_text(encoding="utf-8")

    prog = parse_main_program(src, filename=str(path))
    prog = bind_program(prog, [])
    desugared = desugar(prog, is_main_hole=True)
    ctx, progt = bind(desugared.elabcontext, desugared.program)
    desugared = DesugaredProgram(progt, ctx, desugared.metadata, desugared.constructor_to_type, desugared.constructor_defs)

    sterm = elaborate(desugared.elabcontext, desugared.program, st_top)
    typing_ctx = lower_to_core_context(desugared.elabcontext)
    core_ast = lower_to_core(sterm)
    typing_ctx, core_ast = bind_ids(typing_ctx, core_ast)
    core_ast_anf = ensure_anf(core_ast)

    errors = list(check_type_errors(typing_ctx, core_ast_anf, top))
    assert errors == [], f"Expected no type errors, got: {errors}"
