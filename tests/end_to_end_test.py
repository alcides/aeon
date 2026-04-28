from __future__ import annotations

from aeon.core.bind import bind_ids
from aeon.core.types import top
from aeon.elaboration import elaborate
from aeon.facade.api import LiquidTypeCheckingFailedRelation
from aeon.frontend.anf_converter import ensure_anf
from aeon.sugar.ast_helpers import st_top
from aeon.sugar.bind import bind, bind_program
from aeon.sugar.desugar import DesugaredProgram, desugar
from aeon.sugar.lowering import lower_to_core, lower_to_core_context
from aeon.sugar.parser import parse_main_program, parse_type
from aeon.typechecking.typeinfer import check_type_errors
from aeon.utils.location import FileLocation
from tests.driver import check_compile_expr


def test_anf():
    source = r"""let f : (x:Int) -> (y:Int) -> Int = (\x -> (\y -> x)) in
           let r = f (f 1 2) (f 2 3) in
           r"""
    assert check_compile_expr(source, st_top, 1)


def test_anf_typed():
    source = r"""let f : (x:Int) -> (y:Int) -> {z:Int | z == x } = (\x -> (\y -> x)) in
           let r = f (f 1 2) (f 2 3) in
           r"""
    assert check_compile_expr(source, st_top, 1)


def test_anf_typed_smaller():
    source = r"""let f : (x:Int) -> (y:Int) -> {z:Int | z == x } = (\x -> (\y -> x)) in
           f (f 3 4) 2"""

    source = "let x = 3 in x"
    assert check_compile_expr(source, parse_type("{x:Int | x == 3}"), 3)


def test_annotation():
    source = r""" (1 : Int) """
    assert check_compile_expr(source, parse_type("Int"), 1)


def test_annotation_anf():
    source = r"""let j = (let f : (x:Int) -> {y :Int | y == x} = \x -> x in
                          let a : {x:Int | x == 3} = 3 in
                          f a)
                in j"""
    assert check_compile_expr(source, parse_type("{x:Int | x == 3}"), 3)


def test_annotation_anf2():
    source = r"""let j : {x:Int | x == 3} = (let f : (x:Int) -> {y :Int | y == x} = \x -> x in let a : {x:Int | x == 3} = (let k : {x:Int | x == 3} = 3 in k) in f a) in j"""
    assert check_compile_expr(source, parse_type("{x:Int | x == 3}"), 3)


def test_annotation_anf3():
    source = r"""3 % 2"""
    assert check_compile_expr(source, parse_type("{x:Int | x == 1}"), 1)


def _check_refinement_error_location(
    source: str, filename: str, expected_line: int, expected_col_min: int, expected_col_max: int
) -> None:
    """Helper: parse source, get refinement errors, assert location points to expected range."""
    prog = parse_main_program(source.strip(), filename=filename)
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

    assert len(errors) >= 1, "Expected at least one type error"
    liquid_errors = [e for e in errors if isinstance(e, LiquidTypeCheckingFailedRelation)]
    assert liquid_errors, "Expected LiquidTypeCheckingFailedRelation when refinement fails"

    loc = liquid_errors[0].position()
    assert isinstance(loc, FileLocation)
    assert loc.file == filename
    assert loc.start[0] == expected_line
    assert expected_col_min <= loc.start[1] <= expected_col_max, (
        f"Expected column in [{expected_col_min}, {expected_col_max}], got {loc.start[1]}"
    )


def test_horn_solver_error_location():
    """When the Horn solver fails, the error location should point to the AST element
    being checked as the subtype (e.g. the argument in f(-3)), not the top-level program."""
    source = """
def f (x: {a:Int | a > 0}) : Int = x

def k : Int = f (-3);
"""
    _check_refinement_error_location(source, "test_error.ae", expected_line=3, expected_col_min=14, expected_col_max=22)


def test_horn_solver_error_location_positive_arg():
    """Calling a function that expects negative with a positive argument fails;
    error location should point to the argument expression (2 + 40)."""
    source = """
def g (x: {a:Int | a < 0}) : Int = x

def k : Int = g (2 + 40);
"""
    # Line 3: "def k : Int = g (2 + 40);" - argument "(2 + 40)" is around columns 14-23
    _check_refinement_error_location(
        source, "test_refinement.ae", expected_line=3, expected_col_min=14, expected_col_max=24
    )
