"""Recursive reflection exposes call equations without inventing induction."""

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


def verify(tmp_path, source):
    path = tmp_path / "recursive_reflection.ae"
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 0, no_main=True, check_only=True))
    return list(driver.parse(aeon_code=source, filename=str(path)))


COUNTDOWN = """def count (n:Int | n>=0) : {r:Int | _} decreasing_by [n] :=
  if n = 0 then 0 else count (n-1) + 1;
"""


def test_symbolic_recursive_step(tmp_path):
    assert not verify(tmp_path, COUNTDOWN + """theorem step (n:Int | n>0) : count n = count (n-1)+1 := by smt;""")


def test_concrete_recursive_evaluation(tmp_path):
    assert not verify(tmp_path, COUNTDOWN + """theorem concrete : count 4 = 4 := by smt;""")


def test_false_recursive_claim_rejected(tmp_path):
    assert verify(tmp_path, COUNTDOWN + """theorem false_claim : count 4 = 5 := by smt;""")


@pytest.mark.parametrize("body", ["loop n + 1", "loop (n-1)", "if n=0 then 0 else loop n + 1"])
def test_reflection_cannot_justify_its_own_termination(tmp_path, body):
    assert verify(
        tmp_path,
        f"""def loop (n:Int) : {{r:Int | _ && r > r}} decreasing_by [n] := {body};
      theorem absurd : false := by smt;""",
    )


REVERSE = """import List;
def reverse (xs:List Int) : {r:List Int | _} decreasing_by [List.size xs] :=
  match xs with
  | nil => List.nil
  | cons x tail => List.append (reverse tail) (List.cons x List.nil);
"""


def test_reverse_constructor_equations(tmp_path):
    assert not verify(
        tmp_path,
        REVERSE
        + """
theorem base : reverse List.nil = List.nil := by smt;
theorem step (x:Int) (tail:List Int) :
  reverse (List.cons x tail) = List.append (reverse tail) (List.cons x List.nil) := by smt;
""",
    )


def test_symbolic_induction_uses_reflected_equations(tmp_path):
    assert not verify(
        tmp_path,
        """import List;
def append (xs:List Int) (ys:List Int) : {r:List Int | _}
  decreasing_by [List.size xs] := match xs with
  | nil => ys
  | cons x tail => List.cons x (append tail ys);
theorem append_nil (xs:List Int) : append xs List.nil = xs := by
  induction xs with
  | nil => smt
  | cons x tail ih => simp [ih]
""",
    )


def test_reflection_is_not_induction(tmp_path):
    assert verify(
        tmp_path,
        """import List;
def append (xs:List Int) (ys:List Int) : {r:List Int | _}
  decreasing_by [List.size xs] := match xs with
  | nil => ys
  | cons x tail => List.cons x (append tail ys);
theorem append_nil (xs:List Int) : append xs List.nil = xs := by smt;
""",
    )


def test_reflection_of_another_datatype(tmp_path):
    assert not verify(
        tmp_path,
        """
inductive Tree
| leaf : {t:Tree | rank t = 0}
| fork (left:Tree) (right:Tree) : {t:Tree | rank t = rank left + rank right + 1 && rank left >= 0 && rank right >= 0}
+ rank (t:Tree) : Int

def mirror (t:Tree) : {r:Tree | _} decreasing_by [rank t] :=
  match t with | leaf => Tree.leaf | fork l r => Tree.fork (mirror r) (mirror l);
theorem leaf : mirror Tree.leaf = Tree.leaf := by smt;
theorem step (l:Tree) (r:Tree) : mirror (Tree.fork l r) = Tree.fork (mirror r) (mirror l) := by smt;
""",
    )


def test_reflected_equations_do_not_escape_the_checked_domain(tmp_path):
    assert verify(
        tmp_path,
        """
def restricted (n:Int | n>=0) : {r:Int | _} decreasing_by [n] :=
  if n<0 then restricted n + 1 else 0;
theorem invalid_domain : restricted (0-1) = restricted (0-1)+1 := by smt;
""",
    )


def test_reverse_length_example(tmp_path):
    assert not verify(
        tmp_path,
        REVERSE
        + """
theorem reverse_size (xs:List Int) : List.size (reverse xs) = List.size xs := by
  induction xs with
  | nil => smt
  | cons x tail ih =>
    calc
      List.size (reverse xs) = List.size (List.append (reverse tail) (List.cons x List.nil)) := by smt
      _ = List.size tail + 1 := by simp [ih]
      _ = List.size xs := by smt
""",
    )


def test_polymorphic_recursive_reflection_at_two_instantiations(tmp_path):
    assert not verify(
        tmp_path,
        """import List;
def clone (xs:List a) : {r:List a | _} decreasing_by [List.size xs] :=
  match xs with |nil => List.nil |cons x tail => List.cons x (clone tail);
theorem ints : clone (List.cons 1 List.nil) = List.cons 1 List.nil := by smt;
theorem bools : clone (List.cons true List.nil) = List.cons true List.nil := by smt;
""",
    )


def test_multiple_arguments_are_substituted_simultaneously(tmp_path):
    assert not verify(
        tmp_path,
        """
def swap (n:Int | n>=0) (left:Int) (right:Int) : {r:Int | _} decreasing_by [n] :=
  if n=0 then left else swap (n-1) right left;
theorem odd : swap 3 11 22 = 22 := by smt;
theorem even : swap 4 11 22 = 11 := by smt;
""",
    )


def test_recursive_equations_compose_with_checked_helper_contracts(tmp_path):
    assert not verify(
        tmp_path,
        REVERSE
        + """
theorem length (xs:List Int) : List.size (reverse xs) = List.size xs := by
  induction xs with
  | nil => smt
  | cons x tail ih => simp [ih]
""",
    )


def test_unfolding_limit_leaves_large_goal_unproved():
    from z3 import Solver, sat
    from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
    from aeon.core.types import AbstractionType, t_int
    from aeon.utils.name import Name
    from aeon.verification.reflection import evaluate_reflections
    from aeon.verification.smt import SMTContext, CanonicConstraint, translate

    f, n = Name("count", 0), Name("n", 0)
    var = LiquidVar(n)

    def app(name, *args):
        return LiquidApp(Name(name, 0), list(args))

    body = app(
        "ite",
        app("==", var, LiquidLiteralInt(0)),
        LiquidLiteralInt(0),
        app("+", app("count", app("-", var, LiquidLiteralInt(1))), LiquidLiteralInt(1)),
    )
    ctx = SMTContext([], {str(f): AbstractionType(n, t_int, t_int)}, {}, [], {str(f): ((n,), body)})
    goal = app("==", app("count", LiquidLiteralInt(1000)), LiquidLiteralInt(1000))
    expanded = evaluate_reflections(ctx, goal, {})
    assert 0 < len(expanded.premises) <= 256
    solver = Solver()
    solver.add(translate(CanonicConstraint(expanded, goal)))
    assert solver.check() == sat
