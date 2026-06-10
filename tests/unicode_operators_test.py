"""Lean-style Unicode operator spellings.

Aeon accepts Unicode equivalents for the ordered comparisons, inequality, and
the function/lambda arrows. Each Unicode form is a pure alias for its ASCII
spelling: the parse tree (and therefore the meaning) is identical.
"""

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.sugar.parser import parse_program
from aeon.synthesis.uis.api import SynthesisUI


def _run(source: str):
    cfg = AeonConfig(synthesizer="none", synthesis_ui=SynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(cfg)
    errors = list(driver.parse(aeon_code=source))
    assert not errors, errors
    return driver.run()


# (ascii, unicode) program pairs that must parse to identical ASTs.
EQUIVALENT_PAIRS = [
    (
        "def f (x:Int) (y:Int) : Bool := x <= y;",
        "def f (x:Int) (y:Int) : Bool := x ≤ y;",
    ),
    (
        "def f (x:Int) (y:Int) : Bool := x >= y;",
        "def f (x:Int) (y:Int) : Bool := x ≥ y;",
    ),
    (
        "def f (x:Int) (y:Int) : Bool := x != y;",
        "def f (x:Int) (y:Int) : Bool := x ≠ y;",
    ),
    (
        "def f : (a:Int) -> Int := fun a => a;",
        "def f : (a:Int) → Int := fun a ⇒ a;",
    ),
    (
        "def f : (a:Int) -> Int := fun a => a;",
        "def f : (a:Int) → Int := fun a ↦ a;",
    ),
    (
        "def g (n:Int) : Int := match true with | true => n | false => 0;",
        "def g (n:Int) : Int := match true with | true ⇒ n | false ⇒ 0;",
    ),
]


@pytest.mark.parametrize("ascii_src,unicode_src", EQUIVALENT_PAIRS)
def test_unicode_form_parses_to_same_ast(ascii_src, unicode_src):
    assert str(parse_program(ascii_src)) == str(parse_program(unicode_src))


def test_unicode_program_runs_end_to_end():
    source = r"""
    def absdiff (x:Int) (y:Int) : {r:Int | r ≥ 0} :=
      if x ≥ y then x - y else y - x;

    def classify : (n:Int) → Int :=
      fun n ↦ if n ≤ 0 then 0 else 1;

    def main (_:Int) : Int := absdiff 3 7 + classify (0 - 2);
    """
    assert _run(source) == 4


def test_formatter_emits_unicode():
    # The pretty-printer normalizes ASCII operators to their Unicode spelling.
    from aeon.sugar.bind import bind_program
    from aeon.utils.pprint import pretty_print_node

    src = "def apply (f : (x:Int) -> Int) (v:Int) : {r:Int | r >= 0} := f v;"
    rendered = pretty_print_node(bind_program(parse_program(src), []))
    assert "→" in rendered  # function-type arrow
    assert "≥" in rendered  # ordered comparison
    assert "->" not in rendered and ">=" not in rendered
    # And the Unicode output must round-trip back through the parser.
    parse_program(rendered)


def test_ascii_implication_coexists_with_unicode_arrow():
    # `-->` (implication) must keep lexing as one token even though `→`/`->` are
    # now also arrows; longest-match keeps `-->` distinct from `->`.
    source = r"""
    def p : (a:Bool) → Bool := fun a ↦ (a --> (a ≠ false));
    def main (_:Int) : Bool := p true;
    """
    assert _run(source) is True
