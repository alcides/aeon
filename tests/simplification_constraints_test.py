from __future__ import annotations

from aeon.core.liquid import LiquidVar
from aeon.core.types import BaseType
from aeon.verification.helpers import parse_liquid
from aeon.verification.helpers import simplify_constraint
from aeon.verification.helpers import simplify_expr
from aeon.verification.vcs import Conjunction
from aeon.verification.vcs import Implication
from aeon.verification.vcs import LiquidConstraint


def test_simplify_liquid_right():
    x = parse_liquid("true && a")
    r = simplify_expr(x)
    assert x != r
    assert r == LiquidVar("a")


def test_simplify_liquid_left():
    x = parse_liquid("a && true")
    r = simplify_expr(x)
    assert x != r
    assert r == LiquidVar("a")


def test_simplify_liquid_multiple():
    x = parse_liquid("true && (a && true)")
    r = simplify_expr(x)
    assert x != r
    assert r == LiquidVar("a")


def test_simplify_constraint():
    lc = parse_liquid("true && (a && true)")
    lt = parse_liquid("true && (true && true)")
    x = Conjunction(Conjunction(LiquidConstraint(lt), LiquidConstraint(lc)), LiquidConstraint(lt))
    r = simplify_constraint(x)
    assert r == LiquidConstraint(parse_liquid("a"))


def test_simplify_constraint_implication():
    x = Implication("x", BaseType("Int"), parse_liquid("true"), LiquidConstraint(parse_liquid("a > 0")))
    r = simplify_constraint(x)
    assert r == LiquidConstraint(parse_liquid("a > 0"))


def test_simplify_constraint_implication2():
    x = Implication("x", BaseType("Int"), parse_liquid("x > 0"), LiquidConstraint(parse_liquid("a > 0")))
    r = simplify_constraint(x)
    assert r == LiquidConstraint(parse_liquid("a > 0"))
