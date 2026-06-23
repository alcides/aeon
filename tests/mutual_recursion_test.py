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
  def even (n: {x:Int | x >= 0}) : Bool decreasing_by [n] :=
    if n = 0 then true else odd (n - 1);
  def odd (n: {x:Int | x >= 0}) : Bool decreasing_by [n] :=
    if n = 0 then false else even (n - 1);
end
"""


def test_mutual_even_true():
    errors, result = _run(EVEN_ODD + "def main (x: Int) : Int := if even 10 then 1 else 0;")
    assert errors == []
    assert result == 1


def test_mutual_even_false():
    errors, result = _run(EVEN_ODD + "def main (x: Int) : Int := if even 7 then 1 else 0;")
    assert errors == []
    assert result == 0


def test_mutual_odd_true():
    errors, result = _run(EVEN_ODD + "def main (x: Int) : Int := if odd 5 then 1 else 0;")
    assert errors == []
    assert result == 1


def test_mutual_base_cases():
    assert _run(EVEN_ODD + "def main (x: Int) : Int := if even 0 then 1 else 0;")[1] == 1
    assert _run(EVEN_ODD + "def main (x: Int) : Int := if odd 0 then 1 else 0;")[1] == 0


def test_mutual_three_functions():
    """A group of three functions cycling through one another."""
    src = """
    mutual
      def m0 (n: {x:Int | x >= 0}) : Int decreasing_by [n] :=
        if n = 0 then 0 else m1 (n - 1);
      def m1 (n: {x:Int | x >= 0}) : Int decreasing_by [n] :=
        if n = 0 then 1 else m2 (n - 1);
      def m2 (n: {x:Int | x >= 0}) : Int decreasing_by [n] :=
        if n = 0 then 2 else m0 (n - 1);
    end
    def main (x: Int) : Int := m0 7;
    """
    errors, result = _run(src)
    assert errors == []
    # 7 % 3 == 1  -> after 7 steps we land in m1's base case.
    assert result == 1


def test_mutual_typechecks_without_refinements():
    """No metric is required when the return type carries no refinement."""
    src = """
    mutual
      def ev (n: Int) : Bool := if n = 0 then true else od (n - 1);
      def od (n: Int) : Bool := if n = 0 then false else ev (n - 1);
    end
    def main (x: Int) : Int := if ev 4 then 1 else 0;
    """
    assert _typechecks(src)


def test_mutual_relational_refinement_reflects_sibling():
    """A member's refinement may apply a sibling to its result binder
    (``{r | g r = x}``): the sibling's definition is reflected into SMT, so the
    relation is checked precisely (issue #397, RC category)."""
    src = """
    mutual
      def f (x: {n:Int | n >= 0}) : {r:Int | g r = x} decreasing_by [x] := x;
      def g (x: {n:Int | n >= 0}) : {r:Int | r >= 0} decreasing_by [x] := x;
    end
    """
    assert _typechecks(src)


def test_mutual_relational_refinement_false_rejected():
    """The reflected sibling is precise, not vacuous: a relational spec that does
    not hold (``g r = x + 1`` when ``g`` is the identity) is rejected."""
    src = """
    mutual
      def f (x: {n:Int | n >= 0}) : {r:Int | g r = x + 1} decreasing_by [x] := x;
      def g (x: {n:Int | n >= 0}) : {r:Int | r >= 0} decreasing_by [x] := x;
    end
    """
    assert not _typechecks(src)


def test_mutual_nonterminating_absurd_refinement_rejected():
    """A non-terminating group must not be able to inhabit ``{b:Bool | false}``:
    the cross-function termination obligation (n < n) is unsatisfiable."""
    src = """
    mutual
      def f (n: Int) : {b: Bool | false} decreasing_by [n] := g n;
      def g (n: Int) : {b: Bool | false} decreasing_by [n] := f n;
    end
    def main (x: Int) : Int := 0;
    """
    assert not _typechecks(src)


def test_mutual_reflection_across_two_datatype_sorts():
    """A ``mutual`` group whose members range over *distinct* ADT sorts reflects
    into SMT without a Z3 ``Sort mismatch``.

    Regression: mutually-recursive datatypes ``Tree``/``Forest`` (``Tree``'s
    ``node`` constructor carries a ``Forest`` field, and ``Forest`` is declared
    *after* ``Tree``) used to bind that forward ``Forest`` reference to a fresh,
    distinct id from the ``Forest`` declaration. The SMT backend then minted two
    separate Z3 sorts for the one type, so applying the ``node`` constructor to a
    ``Forest`` argument inside a reflected refinement raised ``Sort mismatch``.
    The relational refinement on ``check`` forces the cross-sort constructor
    application through SMT, exercising the path that used to crash."""
    src = """
    inductive Tree | empty : Tree | node (v: Int) (children: Forest) : Tree
    inductive Forest | leaf : Forest | tcons (t: Tree) (rest: Forest) : Forest
    mutual
      def sizeTree (fuel: {x:Int | x >= 0}) (t: Tree) : Int decreasing_by [fuel] :=
        if fuel = 0 then 0 else (match t with | .empty => 0 | .node v f => 1 + sizeForest (fuel - 1) f);
      def sizeForest (fuel: {x:Int | x >= 0}) (f: Forest) : Int decreasing_by [fuel] :=
        if fuel = 0 then 0 else (match f with | .leaf => 0 | .tcons t rest => sizeTree (fuel - 1) t + sizeForest (fuel - 1) rest);
    end
    def check (x: Forest) : {r:Int | r = sizeTree 0 (.node 0 x)} := sizeTree 0 (.node 0 x);
    def main (z: Int) : Int := sizeTree 10 .empty;
    """
    errors, result = _run(src)
    assert errors == []
    assert result == 0
