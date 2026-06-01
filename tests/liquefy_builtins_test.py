"""Regression tests: built-in SMT operators liquefy to LiquidApp.

Built-in SMT functions (Set operations, comparisons) need no special casing
in ``liquefy_app``; every applied ``SVar`` becomes a ``LiquidApp`` and the
built-in vs. uninterpreted distinction is resolved later in the SMT layer.
These tests pin that behaviour (issue #291, item 1).
"""

from __future__ import annotations

from aeon.core.liquid import LiquidApp
from aeon.core.types import LiquidHornApplication
from aeon.sugar.ast_helpers import mk_binop
from aeon.sugar.lowering import liquefy
from aeon.sugar.program import SApplication, SVar
from aeon.utils.name import Name


def test_comparison_liquefies_to_liquid_app():
    term = mk_binop(Name("<=", 0), SVar(Name("x", 0)), SVar(Name("y", 0)))
    result = liquefy(term)
    assert isinstance(result, LiquidApp)
    assert result.fun == Name("<=", 0)
    assert not isinstance(result, LiquidHornApplication)


def test_set_op_liquefies_to_liquid_app():
    # Set_mem x s
    inner = SApplication(SVar(Name("Set_mem", 0)), SVar(Name("x", 0)))
    term = SApplication(inner, SVar(Name("s", 0)))
    result = liquefy(term)
    assert isinstance(result, LiquidApp)
    assert result.fun == Name("Set_mem", 0)
    assert len(result.args) == 2


def test_user_function_also_liquefies_to_liquid_app():
    # A non-built-in name is treated identically; SMT dispatch happens later.
    term = SApplication(SVar(Name("myMeasure", 0)), SVar(Name("xs", 0)))
    result = liquefy(term)
    assert isinstance(result, LiquidApp)
    assert result.fun == Name("myMeasure", 0)


def test_set_op_through_smt():
    """End-to-end: a refinement using a Set op + comparison verifies via SMT."""
    from aeon.sugar.ast_helpers import st_top
    from tests.driver import check_compile

    code = """
type IntList

def elts : (l:IntList) -> Set = uninterpreted
def size : (l:IntList) -> Int = uninterpreted

def empty : {l:IntList | elts l == Set_empty} = native "[]"

def cons (x:Int) (xs:IntList) : {l:IntList | Set_mem x (elts l)} =
    native "[x] + xs"

def main (_:Int) : Unit =
    a = cons 1 empty;
    print(a)
"""
    assert check_compile(code, st_top)
