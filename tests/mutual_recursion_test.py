"""End-to-end tests for Lean-style ``mutual ... end`` recursion.

A ``mutual`` block co-binds, co-typechecks (with a shared well-founded
termination metric) and co-evaluates a group of definitions that may reference
one another. These tests pin parsing, cross-reference resolution, evaluation and
the mutual-group termination obligation.
"""

from __future__ import annotations

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


def _driver() -> AeonDriver:
    cfg = AeonConfig(
        synthesizer="gp",
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=0,
        no_main=False,
    )
    return AeonDriver(cfg)


def _run(src: str):
    """Compile + evaluate. Returns (errors, result) where result is None on error."""
    d = _driver()
    errors = list(d.parse(aeon_code=src, filename="<test>"))
    if errors:
        return errors, None
    return [], d.run()


def _typechecks(src: str) -> bool:
    d = _driver()
    return list(d.parse(aeon_code=src, filename="<test>")) == []


EVEN_ODD = """
mutual
  def even (n: {x:Int | x >= 0}) : Bool decreasing_by [n] =
    if n == 0 then true else odd (n - 1);
  def odd (n: {x:Int | x >= 0}) : Bool decreasing_by [n] =
    if n == 0 then false else even (n - 1);
end
"""


def test_mutual_even_true():
    errors, result = _run(EVEN_ODD + "def main (x: Int) : Int = if even 10 then 1 else 0;")
    assert errors == []
    assert result == 1


def test_mutual_even_false():
    errors, result = _run(EVEN_ODD + "def main (x: Int) : Int = if even 7 then 1 else 0;")
    assert errors == []
    assert result == 0


def test_mutual_odd_true():
    errors, result = _run(EVEN_ODD + "def main (x: Int) : Int = if odd 5 then 1 else 0;")
    assert errors == []
    assert result == 1


def test_mutual_base_cases():
    assert _run(EVEN_ODD + "def main (x: Int) : Int = if even 0 then 1 else 0;")[1] == 1
    assert _run(EVEN_ODD + "def main (x: Int) : Int = if odd 0 then 1 else 0;")[1] == 0


def test_mutual_three_functions():
    """A group of three functions cycling through one another."""
    src = """
    mutual
      def m0 (n: {x:Int | x >= 0}) : Int decreasing_by [n] =
        if n == 0 then 0 else m1 (n - 1);
      def m1 (n: {x:Int | x >= 0}) : Int decreasing_by [n] =
        if n == 0 then 1 else m2 (n - 1);
      def m2 (n: {x:Int | x >= 0}) : Int decreasing_by [n] =
        if n == 0 then 2 else m0 (n - 1);
    end
    def main (x: Int) : Int = m0 7;
    """
    errors, result = _run(src)
    assert errors == []
    # 7 % 3 == 1  -> after 7 steps we land in m1's base case.
    assert result == 1


def test_mutual_typechecks_without_refinements():
    """No metric is required when the return type carries no refinement."""
    src = """
    mutual
      def ev (n: Int) : Bool = if n == 0 then true else od (n - 1);
      def od (n: Int) : Bool = if n == 0 then false else ev (n - 1);
    end
    def main (x: Int) : Int = if ev 4 then 1 else 0;
    """
    assert _typechecks(src)


def test_mutual_nonterminating_absurd_refinement_rejected():
    """A non-terminating group must not be able to inhabit ``{b:Bool | false}``:
    the cross-function termination obligation (n < n) is unsatisfiable."""
    src = """
    mutual
      def f (n: Int) : {b: Bool | false} decreasing_by [n] = g n;
      def g (n: Int) : {b: Bool | false} decreasing_by [n] = f n;
    end
    def main (x: Int) : Int = 0;
    """
    assert not _typechecks(src)
