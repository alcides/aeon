"""Tests for method-call syntax ``receiver.method`` (issue #27).

A method call dispatches on the receiver's (base) type: ``1.toString`` resolves
to the ``Int.toString`` definition, ``(1.plus 2).toString`` chains. Resolution is
type-directed and happens during elaboration; the surface form parses to
``SApplication(SMethodSelector(method), receiver)``.
"""

from __future__ import annotations

import pytest

from aeon.elaboration import elaborate
from aeon.facade.api import MethodResolutionError
from aeon.sugar.ast_helpers import st_top
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_expression, parse_program
from aeon.sugar.program import (
    SAnonConstructor,
    SApplication,
    SLiteral,
    SMethodSelector,
)
from tests.driver import check_compile


# --- Parsing -----------------------------------------------------------------


def test_parse_method_call_on_literal():
    """``1.toString`` parses to a selector applied to the receiver literal."""
    t = parse_expression("1.toString")
    assert isinstance(t, SApplication)
    assert isinstance(t.fun, SMethodSelector)
    assert t.fun.method.name == "toString"
    assert isinstance(t.arg, SLiteral) and t.arg.value == 1


def test_parse_method_call_with_argument():
    """``1.plus 2`` is ``(1.plus) 2`` — the method result applied to ``2``."""
    t = parse_expression("1.plus 2")
    assert isinstance(t, SApplication)  # outer application to `2`
    assert isinstance(t.arg, SLiteral) and t.arg.value == 2
    inner = t.fun
    assert isinstance(inner, SApplication)
    assert isinstance(inner.fun, SMethodSelector) and inner.fun.method.name == "plus"
    assert isinstance(inner.arg, SLiteral) and inner.arg.value == 1


def test_parse_chained_method_call():
    """``(1.plus 2).toString`` dispatches ``toString`` on the result of ``1.plus 2``."""
    t = parse_expression("(1.plus 2).toString")
    assert isinstance(t, SApplication)
    assert isinstance(t.fun, SMethodSelector) and t.fun.method.name == "toString"
    assert isinstance(t.arg, SApplication)  # the `1.plus 2` receiver


def test_anon_constructor_application_unaffected():
    """Regression: space-separated anonymous-constructor application
    (``.mk .sc_blue 40``) must NOT be reinterpreted as ``.mk`` ``.sc_blue``
    method access — anonymous constructors are never method receivers."""
    t = parse_expression(".mk .sc_blue 40")
    # ((.mk .sc_blue) 40)
    assert isinstance(t, SApplication)
    assert isinstance(t.arg, SLiteral) and t.arg.value == 40
    inner = t.fun
    assert isinstance(inner, SApplication)
    assert isinstance(inner.fun, SAnonConstructor) and inner.fun.name == "mk"
    assert isinstance(inner.arg, SAnonConstructor) and inner.arg.name == "sc_blue"


@pytest.mark.parametrize("src", ["1.5", "-1.0", ".5", "1.5e3", "1e5", "-1.0e-2"])
def test_float_literals_still_parse(src):
    """The float lexer carve-out for ``1.toString`` must not drop signed/exponent
    float forms (e.g. ``-1.0`` in ``v > -1.0``)."""
    assert isinstance(parse_expression(src), SLiteral)


# --- Dotted definition names -------------------------------------------------


def test_dotted_definition_name_parses():
    prog = parse_program('def Int.toString (n:Int) : String = native "str(n)";\ndef main (i:Int) : Int = 0;\n')
    names = [d.name.name for d in prog.definitions]
    assert "Int.toString" in names


# --- End-to-end resolution & evaluation --------------------------------------

_PRELUDE = "def Int.double (n:Int) : Int = n + n;\ndef Int.plus (x:Int) (y:Int) : Int = x + y;\n"


def test_method_call_compiles_and_evaluates():
    src = _PRELUDE + "def main (i:Int) : Int = 3.double;\n"
    assert check_compile(src, st_top, 6)


def test_method_call_with_argument_evaluates():
    # (1.plus 2) == 3, then .double == 6
    src = _PRELUDE + "def main (i:Int) : Int = (1.plus 2).double;\n"
    assert check_compile(src, st_top, 6)


def test_qualified_call_resolves_to_same_definition():
    """A dotted def is also callable directly as ``Int.plus 1 2``."""
    src = _PRELUDE + "def main (i:Int) : Int = Int.plus 4 5;\n"
    assert check_compile(src, st_top, 9)


def test_method_call_on_variable_receiver():
    """``x.method`` for a local variable ``x`` (lexed as a single QUALIFIED_ID)
    is recovered as a method call when ``x`` names no module."""
    src = _PRELUDE + ("def main (i:Int) : Int =\n  let n : Int = 4 in\n  n.double;\n")
    assert check_compile(src, st_top, 8)


def test_chained_method_call_on_variable_receiver():
    src = _PRELUDE + (
        "def main (i:Int) : Int =\n  let n : Int = 3 in\n  n.double.double;\n"  # ((n.double).double) == 12
    )
    assert check_compile(src, st_top, 12)


def test_unknown_method_raises():
    prog = parse_program("def Int.double (n:Int) : Int = n + n;\ndef main (i:Int) : Int = 1.nope;\n")
    desugared = desugar(prog)
    with pytest.raises(MethodResolutionError):
        elaborate(desugared.elabcontext, desugared.program, st_top)
