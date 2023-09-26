from __future__ import annotations

from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidHornApplication
from aeon.core.types import RefinedType
from aeon.core.types import t_int
from aeon.utils.ctx_helpers import build_context
from aeon.verification.helpers import get_abs_example
from aeon.verification.helpers import parse_liquid
from aeon.verification.horn import build_initial_assignment
from aeon.verification.horn import flat
from aeon.verification.horn import fresh
from aeon.verification.horn import get_possible_args
from aeon.verification.horn import merge_assignments
from aeon.verification.horn import solve
from aeon.verification.horn import wellformed_horn
from aeon.verification.vcs import LiquidConstraint


def test_fresh():
    ctx = build_context({"x": t_int})

    t = RefinedType("v", t_int, LiquidHornApplication("?"))
    r = fresh(ctx, t)
    assert r == RefinedType(
        "v_fresh_1",
        t_int,
        LiquidHornApplication(
            "fresh_1",
            [(parse_liquid("x"), "Int"), (parse_liquid("v_fresh_1"), "Int")],
        ),
    )
    assert wellformed_horn(r.refinement)


def test_possible_args():
    hpars = [(parse_liquid("x"), "Int")]
    args = list(get_possible_args(hpars, arity=1))
    assert len(args) == 5


def test_possible_args2():
    hpars = [(parse_liquid("x"), "Int"), (parse_liquid("y"), "Int")]
    args = list(get_possible_args(hpars, arity=2))
    assert len(args) == 100


def test_base_assignment_helper():
    assign = build_initial_assignment(
        LiquidConstraint(
            LiquidHornApplication("k", [(parse_liquid("x"), "Int")])), )
    assert "k" in assign
    assert len(assign["k"]) == 30


def test_base_assignment_helper2():
    assign = build_initial_assignment(
        LiquidConstraint(
            LiquidHornApplication("k", [(parse_liquid("x"), "Int"),
                                        (parse_liquid("y"), "Int")]), ), )
    assert "k" in assign
    assert len(assign["k"]) == 120


def test_merge_assignments():
    assign = build_initial_assignment(
        LiquidConstraint(
            LiquidHornApplication(
                "k",
                [
                    (parse_liquid("x"), "Int"),
                    (parse_liquid("y"), "Int"),
                    (parse_liquid("z"), "Bool"),
                ],
            ), ), )
    t = merge_assignments(assign["k"])
    assert isinstance(t, LiquidApp)


def test_flat():
    ex = get_abs_example()
    res = flat(ex)
    assert len(res) == 3


def test_solve():
    ex = get_abs_example()
    b = solve(ex)
    assert b is True
