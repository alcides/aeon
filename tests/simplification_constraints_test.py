from __future__ import annotations

from aeon.core.bind import bind_lq
from aeon.utils.name import Name

from aeon.core.liquid import LiquidVar
from aeon.core.types import t_int
from aeon.verification.helpers import parse_liquid
from aeon.verification.helpers import simplify_constraint
from aeon.verification.helpers import simplify_expr
from aeon.verification.helpers import split_or_disjuncts
from aeon.verification.helpers import split_or_in_conclusion
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


def test_simplify_constraint_synthesized_var():
    """Synthesized (ANF) variables with only equality are substituted away."""
    anf_name = Name("anf", 1)
    x_name = Name("x", 0)
    z_name = Name("z", 1)

    # forall anf: anf == x, forall z: z == anf + 1, x > 0
    pred_anf = bind_lq(parse_liquid("anf == x"), [("anf", anf_name), ("x", x_name)])
    pred_z = bind_lq(parse_liquid("z == anf + 1"), [("z", z_name), ("anf", anf_name), ("x", x_name)])
    concl = bind_lq(parse_liquid("x > 0"), [("x", x_name)])

    inner = Implication(z_name, t_int, pred_z, LiquidConstraint(concl))
    c = Implication(anf_name, t_int, pred_anf, inner)

    r = simplify_constraint(c)

    # Should become: forall z: z == x + 1, x > 0 (anf substituted by x)
    expected_pred_z = bind_lq(parse_liquid("z == x + 1"), [("z", z_name), ("x", x_name)])
    expected = Implication(z_name, t_int, expected_pred_z, LiquidConstraint(concl))
    assert r == expected, f"Got {r}, expected {expected}"


def test_split_or_disjuncts():
    """OR in conclusion is flattened into separate disjuncts."""
    a = parse_liquid("a > 0")
    b = parse_liquid("b < 0")
    c = parse_liquid("c == 1")

    # a || b
    ab = parse_liquid("a > 0 || b < 0")
    result = split_or_disjuncts(ab)
    assert len(result) == 2
    assert result[0].expr == a
    assert result[1].expr == b

    # (a || b) || c
    abc = parse_liquid("(a > 0 || b < 0) || c == 1")
    result = split_or_disjuncts(abc)
    assert len(result) == 3
    assert result[0].expr == a
    assert result[1].expr == b
    assert result[2].expr == c


def test_split_or_in_conclusion():
    """OR in nested conclusion is split into separate VCs."""
    x_name = Name("x", 0)
    pred = parse_liquid("x == 2")
    concl = parse_liquid("x > 0 || x < 0")

    # forall x: x == 2 => (x > 0 || x < 0)
    c = Implication(x_name, t_int, pred, LiquidConstraint(concl))
    result = split_or_in_conclusion(c)

    assert len(result) == 2
    assert result[0].seq.expr == parse_liquid("x > 0")
    assert result[1].seq.expr == parse_liquid("x < 0")
