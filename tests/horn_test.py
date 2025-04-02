from __future__ import annotations

from aeon.core.liquid import LiquidApp, LiquidVar
from aeon.core.types import LiquidHornApplication
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
from aeon.utils.name import Name


def test_fresh():
    x_name = Name("x")
    v_name = Name("v")
    q_name = Name("?")
    ctx = build_context({x_name: t_int})

    t = RefinedType(v_name, t_int, LiquidHornApplication(q_name, argtypes=[]))
    r = fresh(ctx, t)

    assert isinstance(r, RefinedType)
    assert r.type == t_int
    assert isinstance(r.refinement, LiquidHornApplication)

    assert r.refinement.argtypes == [(LiquidVar(x_name), t_int), (LiquidVar(r.name), t_int)]

    assert wellformed_horn(r.refinement)


def test_possible_args():
    hpars = [(parse_liquid("x"), t_int)]
    args = list(get_possible_args(hpars, arity=1))
    assert len(args) == 5


def test_possible_args2():
    hpars = [(parse_liquid("x"), t_int), (parse_liquid("y"), t_int)]
    args = list(get_possible_args(hpars, arity=2))
    assert len(args) == 100


def test_base_assignment_helper():
    k = Name("k")
    assign = build_initial_assignment(
        LiquidConstraint(LiquidHornApplication(k, [(parse_liquid("x"), t_int)])),
    )
    print(assign)
    assert k in assign
    assert len(assign[k]) == 30


def test_base_assignment_helper2():
    assign = build_initial_assignment(
        LiquidConstraint(
            LiquidHornApplication(Name("k"), [(parse_liquid("x"), t_int), (parse_liquid("y"), t_int)]),
        ),
    )
    k = Name("k")
    assert k in assign
    assert len(assign[k]) == 120


def test_merge_assignments():
    k = Name("k")
    assign = build_initial_assignment(
        LiquidConstraint(
            LiquidHornApplication(
                k,
                [
                    (parse_liquid("x"), t_int),
                    (parse_liquid("y"), t_int),
                    (parse_liquid("z"), t_bool),
                ],
            ),
        ),
    )
    t = merge_assignments(assign[k])
    assert isinstance(t, LiquidApp)


def get_abs_example() -> Constraint:
    hole = LiquidHornApplication(
        Name("k"),
        [(LiquidVar(Name("x")), t_int), (LiquidVar(Name("v")), t_int)],
    )
    hole2 = LiquidHornApplication(
        Name("k"),
        [(LiquidVar(Name("y")), t_int), (LiquidVar(Name("z")), t_int)],
    )

    ap = constraint_builder(
        vs=[(Name("x"), t_int), (Name("c"), t_bool), (Name("v"), t_int)],
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
        vs=[(Name("y"), t_int), (Name("z"), t_int), (Name("c"), t_bool), (Name("b"), t_bool)],
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
