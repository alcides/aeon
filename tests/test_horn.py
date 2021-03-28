from aeon.verification.vcs import Conjunction, Implication, LiquidConstraint
from aeon.core.liquid import (
    LiquidHole,
    LiquidApp,
    LiquidLiteralBool,
    LiquidLiteralInt,
    LiquidVar,
)
from aeon.typing.context import EmptyContext, TypingContext, VariableBinder
from aeon.verification.horn import (
    build_initial_assignment,
    fresh,
    merge_assignments,
    wellformed_horn,
    get_possible_args,
    flat,
    solve,
)
from aeon.core.types import RefinedType, t_int, t_bool
from aeon.utils.ctx_helpers import build_context
from aeon.verification.helpers import get_abs_example


def test_fresh():
    ctx = build_context({"x": t_int})

    t = RefinedType("v", t_int, LiquidHole("?"))
    r = fresh(ctx, t)
    assert r == RefinedType(
        "v_fresh_1", t_int, LiquidHole("fresh_1", [("x", "Int"), ("v_fresh_1", "Int")])
    )
    assert wellformed_horn(r.refinement)


def test_possible_args():
    hpars = [("x", "Int")]
    args = list(get_possible_args(hpars, arity=1))
    assert len(args) == 1


def test_possible_args2():
    hpars = [("x", "Int"), ("y", "Int")]
    args = list(get_possible_args(hpars, arity=2))
    assert len(args) == 4


def test_base_assignment_helper():
    assign = build_initial_assignment(LiquidConstraint(LiquidHole("k", [("x", "Int")])))
    assert "k" in assign
    assert len(assign["k"]) == 6


def test_base_assignment_helper2():
    assign = build_initial_assignment(
        LiquidConstraint(LiquidHole("k", [("x", "Int"), ("y", "Int")]))
    )
    assert "k" in assign
    assert len(assign["k"]) == 24


def test_merge_assignments():
    assign = build_initial_assignment(
        LiquidConstraint(LiquidHole("k", [("x", "Int"), ("y", "Int"), ("z", "Bool")]))
    )
    t = merge_assignments(assign["k"])
    assert isinstance(t, LiquidApp)


def test_flat():
    ex = get_abs_example()
    res = flat(ex)
    assert len(res) == 3


def test_solve():
    ex = get_abs_example()
    b = solve(ex)
    assert b == True
