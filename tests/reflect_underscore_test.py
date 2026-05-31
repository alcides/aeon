from __future__ import annotations

import pytest

from aeon.core.bind import bind_ids
from aeon.core.types import top
from aeon.elaboration import elaborate
from aeon.sugar.ast_helpers import st_top
from aeon.sugar.bind import bind, bind_program
from aeon.sugar.desugar import (
    DesugaredProgram,
    desugar,
    reflect_underscore_in_definitions,
)
from aeon.sugar.lowering import lower_to_core, lower_to_core_context
from aeon.sugar.parser import parse_main_program, parse_program
from aeon.sugar.program import SApplication, SVar
from aeon.sugar.stypes import SRefinedType
from aeon.typechecking.typeinfer import check_type_errors


def _verify(src: str) -> list:
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
    return list(check_type_errors(typing_ctx, core_ast, top))


def test_marker_expands_to_body_equation():
    src = """def double (x:Int) : {y:Int | _} = x + x;
def main (_:Int) : Int = 0"""
    defs = reflect_underscore_in_definitions(parse_program(src).definitions)
    rtype = defs[0].type
    assert isinstance(rtype, SRefinedType)
    # refinement is `y == (x + x)`
    assert isinstance(rtype.refinement, SApplication)
    assert isinstance(rtype.refinement.fun, SApplication)
    assert isinstance(rtype.refinement.fun.fun, SVar)
    assert rtype.refinement.fun.fun.name.name == "=="


def test_reflected_body_is_visible_at_call_site():
    src = """def double (x:Int) : {y:Int | _} = x + x;
def inc (x:Int) : {y:Int | _} = x + 1;
def check : {b:Bool | b} = double 5 == 10;
def check2 : {b:Bool | b} = inc (double 3) == 7;
def main (_:Int) : Int = 0"""
    assert _verify(src) == []


def test_marker_composes_with_manual_refinement():
    # The body must satisfy the manual conjunct too: with a non-negative input,
    # `x + x >= 0` holds, so `_ && y >= 0` is provable.
    src = """def double (x:{v:Int | v >= 0}) : {y:Int | _ && y >= 0} = x + x;
def check : {b:Bool | b} = double 5 == 10;
def main (_:Int) : Int = 0"""
    assert _verify(src) == []


def test_wrong_postcondition_fails_to_verify():
    src = """def double (x:Int) : {y:Int | _} = x + x;
def check : {b:Bool | b} = double 5 == 11;
def main (_:Int) : Int = 0"""
    assert _verify(src) != []


def test_no_marker_is_left_unchanged():
    src = """def double (x:Int) : {y:Int | y > 0} = x + x;
def main (_:Int) : Int = 0"""
    defs = parse_program(src).definitions
    out = reflect_underscore_in_definitions(defs)
    assert out[0] is defs[0]


def test_underscore_parameter_name_is_not_a_marker():
    src = """def const (_:Unit) : {y:Int | y == 3} = 3;
def main (_:Int) : Int = 0"""
    defs = parse_program(src).definitions
    out = reflect_underscore_in_definitions(defs)
    assert out[0] is defs[0]


def test_if_body_reflects_and_verifies():
    # An if-then-else body lowers to `ite` in the refinement and verifies.
    src = """def absv (x:Int) : {y:Int | _} = if x < 0 then (0 - x) else x;
def check : {b:Bool | b} = absv (0 - 5) == 5;
def check2 : {b:Bool | b} = absv 3 == 3;
def main (_:Int) : Int = 0"""
    assert _verify(src) == []


def test_if_body_wrong_claim_fails():
    src = """def absv (x:Int) : {y:Int | _} = if x < 0 then (0 - x) else x;
def check : {b:Bool | b} = absv (0 - 5) == 4;
def main (_:Int) : Int = 0"""
    assert _verify(src) != []


def test_native_body_rejected_with_clear_error():
    src = """def foo (x:Int) : {y:Int | _} = native "x";
def main (_:Int) : Int = 0"""
    with pytest.raises(TypeError, match="native and uninterpreted"):
        reflect_underscore_in_definitions(parse_program(src).definitions)


def test_recursive_body_rejected_with_clear_error():
    src = """def fact (n:Int) : {r:Int | _} = n * fact (n - 1);
def main (_:Int) : Int = 0"""
    with pytest.raises(TypeError, match="recursive"):
        reflect_underscore_in_definitions(parse_program(src).definitions)
