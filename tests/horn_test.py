from __future__ import annotations

from aeon.core.liquid import LiquidApp, LiquidVar
from aeon.core.types import BaseType, LiquidHornApplication
from aeon.core.types import RefinedType
from aeon.core.types import t_int
from aeon.utils.ctx_helpers import build_context
from aeon.verification.helpers import conj, constraint_builder, end, imp, parse_liquid
from aeon.verification.horn import build_initial_assignment
from aeon.verification.horn import flat
from aeon.verification.horn import fresh
from aeon.verification.horn import get_possible_args
from aeon.verification.horn import merge_assignments
from aeon.verification.horn import solve
from aeon.verification.horn import wellformed_horn
from aeon.verification.vcs import Constraint, LiquidConstraint
from aeon.core.types import t_bool


def test_fresh():
    ctx = build_context({"x": t_int})

    t = RefinedType("v", t_int, LiquidHornApplication("?", argtypes=[]))
    r = fresh(ctx, t)
    assert r == RefinedType(
        "v_fresh_1",
        t_int,
        LiquidHornApplication(
            "fresh_1",
            [(parse_liquid("x"), BaseType("Int")), (parse_liquid("v_fresh_1"), BaseType("Int"))],
        ),
    )
    assert wellformed_horn(r.refinement)


def test_possible_args():
    hpars = [(parse_liquid("x"), BaseType("Int"))]
    args = list(get_possible_args(hpars, arity=1))
    assert len(args) == 5


def test_possible_args2():
    hpars = [(parse_liquid("x"), BaseType("Int")), (parse_liquid("y"), BaseType("Int"))]
    args = list(get_possible_args(hpars, arity=2))
    assert len(args) == 100


def test_base_assignment_helper():
    assign = build_initial_assignment(
        LiquidConstraint(LiquidHornApplication("k", [(parse_liquid("x"), BaseType("Int"))])),
    )
    assert "k" in assign
    assert len(assign["k"]) == 30


def test_base_assignment_helper2():
    assign = build_initial_assignment(
        LiquidConstraint(
            LiquidHornApplication("k", [(parse_liquid("x"), BaseType("Int")), (parse_liquid("y"), BaseType("Int"))]),
        ),
    )
    assert "k" in assign
    assert len(assign["k"]) == 120


def test_merge_assignments():
    assign = build_initial_assignment(
        LiquidConstraint(
            LiquidHornApplication(
                "k",
                [
                    (parse_liquid("x"), BaseType("Int")),
                    (parse_liquid("y"), BaseType("Int")),
                    (parse_liquid("z"), BaseType("Bool")),
                ],
            ),
        ),
    )
    t = merge_assignments(assign["k"])
    assert isinstance(t, LiquidApp)


def get_abs_example() -> Constraint:
    hole = LiquidHornApplication(
        "k",
        [(LiquidVar("x"), t_int), (LiquidVar("v"), t_int)],
    )
    hole2 = LiquidHornApplication(
        "k",
        [(LiquidVar("y"), t_int), (LiquidVar("z"), t_int)],
    )

    ap = constraint_builder(
        vs=[("x", t_int), ("c", t_bool), ("v", t_int)],
        exp=imp(
            "c == (0 <= x)",
            conj(
                imp(
                    "c",
                    imp("v == x", end(hole)),
                ),
                imp("!c", imp("v == (0 - x)", end(hole))),
            ),
        ),
    )

    cp = constraint_builder(
        vs=[("y", t_int), ("z", t_int), ("c", t_bool), ("b", t_bool)],
        exp=imp(hole2, imp("c == (0 <= z)", imp("b == c", end("b")))),
    )

    return conj(ap, cp)


def test_flat():
    ex = get_abs_example()
    res = flat(ex)
    assert len(res) == 3


def test_solve():
    ex = get_abs_example()
    b = solve(ex)
    assert b is True
