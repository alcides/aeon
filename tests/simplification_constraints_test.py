from __future__ import annotations

from aeon.core.bind import bind_lq
from aeon.utils.name import Name

from aeon.core.liquid import LiquidVar
from aeon.core.types import t_int
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
    assert r == LiquidVar(Name("a"))


def test_simplify_liquid_left():
    x = parse_liquid("a && true")
    r = simplify_expr(x)
    assert x != r
    assert r == LiquidVar(Name("a"))


def test_simplify_liquid_multiple():
    x = parse_liquid("true && (a && true)")
    r = simplify_expr(x)
    assert x != r
    assert r == LiquidVar(Name("a"))


def test_simplify_constraint():
    lc = parse_liquid("true && (a && true)")
    lt = parse_liquid("true && (true && true)")
    x = Conjunction(Conjunction(LiquidConstraint(lt), LiquidConstraint(lc)), LiquidConstraint(lt))
    r = simplify_constraint(x)
    assert r == LiquidConstraint(parse_liquid("a"))


def test_simplify_constraint_implication():
    x = Implication(Name("x"), t_int, parse_liquid("true"), LiquidConstraint(parse_liquid("a > 0")))
    r = simplify_constraint(x)
    assert r == LiquidConstraint(parse_liquid("a > 0"))


def test_simplify_constraint_implication2():
    x_gt_0 = bind_lq(parse_liquid("x > 0"), [("x", Name("x", 42))])
    a_gt_0 = bind_lq(parse_liquid("a > 0"), [("a", Name("a", 42))])

    x = Implication(Name("x", 42), t_int, x_gt_0, LiquidConstraint(a_gt_0))
    r = simplify_constraint(x)
    assert r == LiquidConstraint(a_gt_0), f"{r} is not a > 0"
