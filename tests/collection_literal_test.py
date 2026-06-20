"""Lean-style collection literals: ``[1, 2, 3]`` (List) and ``#[1, 2, 3]`` (Array).

``[`` is unambiguously a list literal: type application uses ``{t}`` (e.g.
``List.nil{Int}``), so the two never collide. ``#[…]`` is an array literal (the
COMMENT lexer carves out ``#[`` so it is not read as a comment). Literals desugar
to ``List.cons``/``List.nil`` and ``Array.new``/``Array.append``; element types
are inferred by elaboration.
"""

from __future__ import annotations

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


def _run(src: str) -> object:
    cfg = AeonConfig(synthesizer="gp", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=False)
    d = AeonDriver(cfg)
    assert d.parse(aeon_code=src, filename="<t>") == [], "expected no parse/type errors"
    return d.run()


def test_list_literal_length():
    assert _run("import List;\ndef main (u:Int) : Int := List.length [10, 20, 30];") == 3


def test_array_literal_length():
    assert _run("import Array;\ndef main (u:Int) : Int := Array.length #[5, 6, 7, 8];") == 4


def test_empty_list_literal_with_annotation():
    src = "import List;\ndef main (u:Int) : Int := let e : (List Int) := [] in List.length e;"
    assert _run(src) == 0


def test_empty_array_literal():
    assert _run("import Array;\ndef main (u:Int) : Int := Array.length #[];") == 0


def test_list_literal_as_spaced_application_argument():
    src = """
import List;
def f (l: (List Int)) : Int := List.length l;
def main (u:Int) : Int := f [1, 2];
"""
    assert _run(src) == 2


def test_method_dot_on_list_literal():
    # ``.length`` attached to the closing ``]`` is a method call on the literal.
    assert _run("import List;\ndef main (u:Int) : Int := [1, 2, 3, 4, 5].length;") == 5


def test_nested_list_literal():
    assert _run("import List;\ndef main (u:Int) : Int := List.length [[1, 2], [3]];") == 2


def test_type_application_uses_braces():
    # Type application is ``{t}`` (``[`` is reserved for list literals), so
    # ``List.nil{Int}`` instantiates the empty list at ``Int``.
    assert _run("import List;\ndef main (u:Int) : Int := List.length (List.nil{Int});") == 0


def test_list_literal_elements_evaluate():
    # Elements are arbitrary expressions; sum the list via a fold.
    src = """
import List;
def add (x:Int) (y:Int) : Int := x + y;
def main (u:Int) : Int := List.foldr add 0 [1, 2, 3, 4];
"""
    assert _run(src) == 10
