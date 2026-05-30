from __future__ import annotations

from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidTerm, LiquidVar
from aeon.core.types import AbstractionType
from aeon.core.types import LiquidHornApplication
from aeon.core.types import RefinedType
from aeon.core.types import TypeConstructor
from aeon.core.types import TypeVar
from aeon.core.types import t_int
from aeon.typechecking.context import TypingContext, UninterpretedBinder
from aeon.typechecking.entailment import entailment
from aeon.utils.ctx_helpers import build_context
from aeon.verification.helpers import conj, constraint_builder, end, imp, parse_liquid
from aeon.verification.helpers import simplify_constraint_fixpoint
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


def test_fresh_admits_type_var_context_vars():
    """Polymorphism (#288): ``TypeVar``-typed context variables (bare or refined)
    become qualifier-atom slots, projected onto their base type variable, while
    the monomorphic atom set is left unchanged (refined-over-``TypeConstructor``
    and function-typed vars stay excluded)."""
    a_name = Name("a")
    x_name = Name("x")  # x : a            (bare TypeVar)
    w_name = Name("w")  # w : {_:a | _}    (refined over a TypeVar)
    y_name = Name("y")  # y : {_:Int | _}  (refined over a TypeConstructor)
    z_name = Name("z")  # z : Int          (bare TypeConstructor)
    f_name = Name("f")  # f : Int -> Int   (function, excluded)
    v_name = Name("v")
    q_name = Name("?")

    tv = TypeVar(a_name)
    refined_tv = RefinedType(Name("_"), tv, LiquidLiteralBool(True))
    refined_int = RefinedType(Name("_"), t_int, LiquidLiteralBool(True))
    fun_ty = AbstractionType(Name("n"), t_int, t_int)
    ctx = build_context({x_name: tv, w_name: refined_tv, y_name: refined_int, z_name: t_int, f_name: fun_ty})

    t = RefinedType(v_name, tv, LiquidHornApplication(q_name, argtypes=[]))
    r = fresh(ctx, t)

    assert isinstance(r, RefinedType)
    assert isinstance(r.refinement, LiquidHornApplication)

    slots = dict(r.refinement.argtypes)
    # Bare TypeVar var survives with its TypeVar sort.
    assert slots[LiquidVar(x_name)] == tv
    # Refined-over-TypeVar var projects onto its base type variable.
    assert slots[LiquidVar(w_name)] == tv
    # Bare TypeConstructor var survives (unchanged behavior).
    assert slots[LiquidVar(z_name)] == t_int
    # The self-variable (also of TypeVar sort) survives too.
    assert slots[LiquidVar(r.name)] == tv
    # Refined-over-TypeConstructor var stays excluded (unchanged behavior).
    assert LiquidVar(y_name) not in slots
    # The function-typed var is not admissible and is dropped.
    assert LiquidVar(f_name) not in slots

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


def _liquid_function_names(t: LiquidTerm) -> set[Name]:
    """All function names applied anywhere inside a liquid term."""
    match t:
        case LiquidApp(fun, args):
            names = {fun}
            for a in args:
                names |= _liquid_function_names(a)
            return names
        case _:
            return set()


def _measure_context() -> tuple[TypingContext, Name]:
    """A context with a user type ``Dataset`` and a custom measure
    ``feats : (ds: Dataset) -> Int`` declared uninterpreted."""
    dataset = TypeConstructor(Name("Dataset", 0))
    feats = Name("feats", 0)
    ctx = TypingContext()
    ctx.entries.append(UninterpretedBinder(feats, AbstractionType(Name("ds", 0), dataset, t_int)))
    return ctx, feats


def test_initial_assignment_without_context_ignores_measures():
    """Without a typing context, candidate generation is unchanged (prelude only)."""
    k = Name("k")
    hole = LiquidHornApplication(k, [(parse_liquid("x"), t_int)])
    assign = build_initial_assignment(LiquidConstraint(hole))
    assert k in assign
    assert len(assign[k]) == 30


def test_initial_assignment_uses_custom_measures():
    """A custom measure in the typing context is woven into candidate predicates
    for a hole over that measure's domain (e.g. ``feats(arg_0) <= 0``)."""
    ctx, feats = _measure_context()
    dataset = TypeConstructor(Name("Dataset", 0))
    k = Name("k")
    hole = LiquidHornApplication(k, [(parse_liquid("d"), dataset)])

    base = build_initial_assignment(LiquidConstraint(hole))
    with_ctx = build_initial_assignment(LiquidConstraint(hole), typing_ctx=ctx)

    # The measure introduces strictly more candidates than the prelude alone.
    assert len(with_ctx[k]) > len(base[k])

    # At least one candidate actually mentions the custom measure.
    assert any(feats in _liquid_function_names(c) for c in with_ctx[k])


def _eq(a: LiquidTerm, b: LiquidTerm) -> LiquidApp:
    return LiquidApp(Name("==", 0), [a, b])


def test_solve_discharges_goal_requiring_a_measure():
    """The hole's only viable refinement mentions a custom measure, so the
    solver must *synthesise* a measure-based predicate to discharge the goal.

    Two occurrences of the same hole ``?k(_, _)`` over ``(Dataset, Int)``:

        forall d, n | n == feats(d)  =>  ?k(d, n)        (k as head)
        forall p, m | ?k(p, m)       =>  feats(p) == m   (k as premise)

    The second implication only holds if ``?k`` is strong enough to carry
    ``feats(arg_0) == arg_1`` — a predicate that can only be generated once
    the custom measure ``feats`` is plumbed into candidate generation.
    """
    ctx, feats = _measure_context()
    dataset = TypeConstructor(Name("Dataset", 0))
    k = Name("k")

    d, n = Name("d", 0), Name("n", 0)
    head_hole = LiquidHornApplication(k, [(LiquidVar(d), dataset), (LiquidVar(n), t_int)])
    ap = constraint_builder(
        vs=[(d, dataset), (n, t_int)],
        exp=imp(_eq(LiquidVar(n), LiquidApp(feats, [LiquidVar(d)])), end(head_hole)),
    )

    p, m = Name("p", 0), Name("m", 0)
    prem_hole = LiquidHornApplication(k, [(LiquidVar(p), dataset), (LiquidVar(m), t_int)])
    cp = constraint_builder(
        vs=[(p, dataset), (m, t_int)],
        exp=imp(prem_hole, end(_eq(LiquidApp(feats, [LiquidVar(p)]), LiquidVar(m)))),
    )

    assert entailment(ctx, conj(ap, cp)) is True


def test_simplify_constraint_fixpoint_reduces_trivial_boolean_structure():
    c = LiquidConstraint(
        LiquidApp(
            Name("&&", 0),
            [
                LiquidApp(Name("==", 0), [LiquidVar(Name("x")), LiquidVar(Name("x"))]),
                LiquidLiteralBool(True),
            ],
        )
    )
    s = simplify_constraint_fixpoint(c)
    assert isinstance(s, LiquidConstraint)
    assert s.expr == LiquidLiteralBool(True)
