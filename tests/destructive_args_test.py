"""Tests for destructive function arguments.

A parameter prefixed with ``!`` (e.g. ``def f (!x: Int)``) marks the parameter
as destructive: passing a variable in that position consumes it, so the
variable becomes unavailable in the surrounding scope.
"""

from __future__ import annotations

from aeon.core.bind import bind_ids
from aeon.core.types import top, AbstractionType
from aeon.core.terms import Rec
from aeon.elaboration import elaborate
from aeon.facade.api import CoreDestroyedVariableUseError
from aeon.frontend.anf_converter import ensure_anf
from aeon.sugar.desugar import desugar
from aeon.sugar.lowering import lower_to_core, lower_to_core_context
from aeon.sugar.parser import parse_program
from aeon.sugar.stypes import SAbstractionType
from aeon.typechecking.typeinfer import check_type_errors


def _typecheck(source: str):
    prog = parse_program(source)
    desugared = desugar(prog)
    sterm = elaborate(desugared.elabcontext, desugared.program)
    core_ast = lower_to_core(sterm)
    typing_ctx = lower_to_core_context(desugared.elabcontext)
    typing_ctx, core_ast = bind_ids(typing_ctx, core_ast)
    core_ast_anf = ensure_anf(core_ast)
    return list(check_type_errors(typing_ctx, core_ast_anf, top))


def _find_rec(t, name: str):
    if isinstance(t, Rec):
        if t.var_name.name == name:
            return t
        return _find_rec(t.var_value, name) or _find_rec(t.body, name)
    return None


def test_parser_records_destructive_flag():
    prog = parse_program("def f (!x: Int) : Int = x;")
    f = next(d for d in prog.definitions if d.name.name == "f")
    assert f.destructive_args == (True,)


def test_parser_records_non_destructive_flag():
    prog = parse_program("def f (x: Int) : Int = x;")
    f = next(d for d in prog.definitions if d.name.name == "f")
    assert f.destructive_args == (False,)


def test_parser_records_mixed_destructive_flags():
    prog = parse_program("def f (!x: Int) (y: Int) (!z: Int) : Int = x;")
    f = next(d for d in prog.definitions if d.name.name == "f")
    assert f.destructive_args == (True, False, True)


def test_destructive_flag_reaches_sugar_abstraction_type():
    """The destructive flag should be propagated to ``SAbstractionType.destructive``
    when a definition is converted into the program ``SRec`` chain."""
    from aeon.sugar.program import SRec

    prog = parse_program("def f (!x: Int) : Int = x;")
    desugared = desugar(prog)
    # Walk the program SRec chain looking for the binding for f.
    cur = desugared.program
    found = None
    while isinstance(cur, SRec):
        if cur.var_name.name == "f":
            found = cur
            break
        cur = cur.body
    assert found is not None
    ty = found.var_type
    assert isinstance(ty, SAbstractionType)
    assert ty.destructive is True


def test_destructive_flag_reaches_core_abstraction_type():
    prog = parse_program("def f (!x: Int) : Int = x;")
    desugared = desugar(prog)
    sterm = elaborate(desugared.elabcontext, desugared.program)
    core_ast = lower_to_core(sterm)
    f_rec = _find_rec(core_ast, "f")
    assert f_rec is not None
    assert isinstance(f_rec.var_type, AbstractionType)
    assert f_rec.var_type.destructive is True


def test_use_after_destruction_in_let_body_errors():
    """Using a variable consumed by a destructive arg should be a type error."""
    source = """
def f (!x: Int | x > 0) : Int = x;

def main (_:Int) : Int =
    let a : Int | a > 0 = 5 in
    let y = f a in
    a + 1;
"""
    errors = _typecheck(source)
    destroyed_errors = [e for e in errors if isinstance(e, CoreDestroyedVariableUseError)]
    assert destroyed_errors, f"Expected CoreDestroyedVariableUseError, got: {errors}"


def test_no_use_after_destruction_is_ok():
    """If we never reference the variable again, the program type-checks."""
    source = """
def f (!x: Int | x > 0) : Int = x;

def main (_:Int) : Int =
    let a : Int | a > 0 = 5 in
    let y = f a in
    y + 1;
"""
    errors = _typecheck(source)
    assert not errors, f"Expected no errors, got: {errors}"


def test_non_destructive_does_not_consume():
    """A non-destructive parameter leaves the argument variable available."""
    source = """
def g (x: Int | x > 0) : Int = x;

def main (_:Int) : Int =
    let a : Int | a > 0 = 5 in
    let y = g a in
    a + 1;
"""
    errors = _typecheck(source)
    assert not errors, f"Expected no errors, got: {errors}"


def test_destruction_inside_branch_does_not_leak_to_other_branch():
    """Destruction inside one If branch must not affect the sibling branch."""
    source = """
def f (!x: Int | x > 0) : Int = x;

def main (_:Int) : Int =
    let a : Int | a > 0 = 5 in
    let b : Int | b > 0 = 10 in
    if a == b then
        let y = f a in y
    else
        b;
"""
    errors = _typecheck(source)
    assert not errors, f"Expected no errors, got: {errors}"


def test_two_destructive_args_consume_both_variables():
    """When a function has two destructive parameters, both arguments are consumed."""
    source = """
def f (!x: Int | x > 0) (!y: Int | y > 0) : Int = x + y;

def main (_:Int) : Int =
    let a : Int | a > 0 = 5 in
    let b : Int | b > 0 = 7 in
    let r = f a b in
    a + 1;
"""
    errors = _typecheck(source)
    destroyed_errors = [e for e in errors if isinstance(e, CoreDestroyedVariableUseError)]
    assert destroyed_errors, f"Expected CoreDestroyedVariableUseError, got: {errors}"


def test_mixed_destructive_only_consumes_marked_param():
    """Only the destructive position consumes its argument."""
    source = """
def f (!x: Int | x > 0) (y: Int | y > 0) : Int = x + y;

def main (_:Int) : Int =
    let a : Int | a > 0 = 5 in
    let b : Int | b > 0 = 7 in
    let r = f a b in
    b + 1;
"""
    errors = _typecheck(source)
    assert not errors, f"Expected no errors (only `a` consumed), got: {errors}"


def test_use_of_consumed_arg_in_mixed_signature_errors():
    source = """
def f (!x: Int | x > 0) (y: Int | y > 0) : Int = x + y;

def main (_:Int) : Int =
    let a : Int | a > 0 = 5 in
    let b : Int | b > 0 = 7 in
    let r = f a b in
    a + 1;
"""
    errors = _typecheck(source)
    destroyed_errors = [e for e in errors if isinstance(e, CoreDestroyedVariableUseError)]
    assert destroyed_errors, f"Expected CoreDestroyedVariableUseError, got: {errors}"
