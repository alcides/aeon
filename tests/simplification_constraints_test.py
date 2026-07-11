from __future__ import annotations

from aeon.core.bind import bind_lq
from aeon.utils.name import Name

from aeon.core.liquid import LiquidLiteralBool, LiquidLiteralInt, LiquidVar
from aeon.core.types import t_int, TypeConstructor
from aeon.verification.helpers import parse_liquid
from aeon.verification.helpers import prepare_vc_for_display
from aeon.verification.helpers import remove_inert_preconditions
from aeon.verification.helpers import render_constraint_for_display
from aeon.verification.helpers import simplify_constraint
from aeon.verification.helpers import simplify_constraint_fixpoint
from aeon.verification.helpers import simplify_expr
from aeon.verification.helpers import vc_simplification_steps
from aeon.verification.helpers import split_and_in_conclusion
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


def test_vc_simplification_steps_are_ordered_and_end_simplified():
    # A VC with a trivially-true precondition and an already-present conjunct in
    # the conclusion has room to simplify, so the chain has more than one step.
    x = Implication(Name("x"), t_int, parse_liquid("true"), LiquidConstraint(parse_liquid("a > 0")))
    steps = vc_simplification_steps(x)
    assert len(steps) >= 1
    # Every step is a (label, text) pair.
    for label, text in steps:
        assert isinstance(label, str) and isinstance(text, str)
    # The last step must equal the fully simplified rendering used in errors.
    assert steps[-1][1] == render_constraint_for_display(prepare_vc_for_display(x))
    # Consecutive steps never render identically (duplicates are collapsed).
    texts = [t for _, t in steps]
    assert all(texts[i] != texts[i + 1] for i in range(len(texts) - 1))


def test_vc_simplification_steps_show_progression():
    # ∀x, true => (a > 0) simplifies to just (a > 0): the original shows the
    # implication turnstile, the final drops it, so there are two distinct steps.
    x = Implication(Name("x"), t_int, parse_liquid("true"), LiquidConstraint(parse_liquid("a > 0")))
    steps = vc_simplification_steps(x)
    labels = [label for label, _ in steps]
    assert labels[0] == "Original"
    assert len(steps) >= 2
    # The original renders the implication turnstile; the simplified form does not.
    assert "====>" in steps[0][1]
    assert "====>" not in steps[-1][1]


def test_simplify_constraint_implication2():
    x_gt_0 = bind_lq(parse_liquid("x > 0"), [("x", Name("x", 42))])
    a_gt_0 = bind_lq(parse_liquid("a > 0"), [("a", Name("a", 42))])

    x = Implication(Name("x", 42), t_int, x_gt_0, LiquidConstraint(a_gt_0))
    r = simplify_constraint(x)
    assert r == LiquidConstraint(a_gt_0), f"{r} is not a > 0"


def test_simplify_constraint_synthesized_var():
    """Equality binders are substituted away for all variables.

    When a ``forall`` binder carries an equality predicate (e.g. ``_y == x``
    or ``z == expr``), ``simplify_constraint`` substitutes the variable with
    its equal expression and drops the binder.  This applies to synthesized
    existential binders (``_y``) as well as any other variable.
    """
    y_name = Name("_y", 1)
    x_name = Name("x", 0)
    z_name = Name("z", 1)

    # forall _y: _y == x, forall z: z == _y + 1, x > 0
    pred_y = bind_lq(parse_liquid("_y == x"), [("_y", y_name), ("x", x_name)])
    pred_z = bind_lq(parse_liquid("z == _y + 1"), [("z", z_name), ("_y", y_name), ("x", x_name)])
    concl = bind_lq(parse_liquid("x > 0"), [("x", x_name)])

    inner = Implication(z_name, t_int, pred_z, LiquidConstraint(concl))
    c = Implication(y_name, t_int, pred_y, inner)

    r = simplify_constraint(c)

    # Both _y and z are eliminated: _y → x, then z → (x + 1) which doesn't
    # appear in the conclusion, so the result is just ``x > 0``.
    assert r == LiquidConstraint(concl), f"Got {r}, expected {LiquidConstraint(concl)}"


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


def test_split_and_in_conclusion():
    """AND in nested conclusion is split into separate VCs."""
    x_name = Name("x", 0)
    pred = parse_liquid("x > 0")
    concl = parse_liquid("x > 1 && x < 10")

    c = Implication(x_name, t_int, pred, LiquidConstraint(concl))
    result = split_and_in_conclusion(c)

    assert len(result) == 2
    assert result[0].seq.expr == parse_liquid("x > 1")
    assert result[1].seq.expr == parse_liquid("x < 10")


def test_remove_inert_precondition_unused_binder():
    """Drop preconditions whose variables do not appear in the goal."""
    i_name = Name("i", 1)
    x_name = Name("x", 0)
    irrelevant = bind_lq(parse_liquid("len i >= 0"), [("i", i_name)])
    goal = bind_lq(parse_liquid("x > 0"), [("x", x_name)])

    c = Implication(i_name, t_int, irrelevant, LiquidConstraint(goal))
    r = remove_inert_preconditions(c)
    assert r == LiquidConstraint(goal)


def test_keep_false_precondition():
    """False preconditions are kept because they explain an impossible context."""
    n_name = Name("n", 1)
    pred = bind_lq(parse_liquid("false"), [("n", n_name)])
    goal = bind_lq(parse_liquid("n > 0"), [("n", n_name)])

    c = Implication(n_name, t_int, pred, LiquidConstraint(goal))
    r = remove_inert_preconditions(c)
    assert r == c


def test_keep_contradictory_preconditions():
    """Contradictory preconditions are kept because they are diagnostically relevant."""
    x_name = Name("x", 0)
    low = bind_lq(parse_liquid("x > 10"), [("x", x_name)])
    high = bind_lq(parse_liquid("x < 0"), [("x", x_name)])
    goal = bind_lq(parse_liquid("x == 5"), [("x", x_name)])

    inner = Implication(x_name, t_int, high, LiquidConstraint(goal))
    c = Implication(x_name, t_int, low, inner)
    r = remove_inert_preconditions(c)
    assert r == c


def test_prepare_vc_for_display_drops_irrelevant():
    i_name = Name("i", 1)
    x_name = Name("x", 0)
    irrelevant = bind_lq(parse_liquid("len i >= 0"), [("i", i_name)])
    goal = bind_lq(parse_liquid("x > 0"), [("x", x_name)])

    c = Implication(i_name, t_int, irrelevant, LiquidConstraint(goal))
    r = prepare_vc_for_display(c)
    assert r == LiquidConstraint(goal)


def test_simplify_redundant_conclusion():
    """Simplifies implications by removing redundant conjuncts from conclusion.

    If premise is 'a > 0' and conclusion is 'a > 0 && b > 0',
    the simplified conclusion should be just 'b > 0'.
    """
    a_name = Name("a", 42)
    a_gt_0 = bind_lq(parse_liquid("a > 0"), [("a", a_name)])
    a_gt_0_and_b_gt_0 = bind_lq(parse_liquid("a > 0 && b > 0"), [("a", a_name), ("b", Name("b", 43))])
    b_gt_0 = bind_lq(parse_liquid("b > 0"), [("b", Name("b", 43))])

    # forall a: a > 0 => a > 0 && b > 0
    c = Implication(a_name, t_int, a_gt_0, LiquidConstraint(a_gt_0_and_b_gt_0))
    r = simplify_constraint(c)

    # Should simplify to: forall a: a > 0 => b > 0
    expected = Implication(a_name, t_int, a_gt_0, LiquidConstraint(b_gt_0))
    assert r == expected, f"Got {r}, expected {expected}"


def test_simplify_redundant_conclusion_multiple_conjuncts():
    """Simplifies implications with multiple redundant conjuncts.

    If premise is 'a > 0 && b > 0' and conclusion is 'a > 0 && b > 0 && c > 0',
    the simplified conclusion should be just 'c > 0'.
    """
    x_name = Name("x", 42)
    premise = bind_lq(parse_liquid("a > 0 && b > 0"), [("a", Name("a", 43)), ("b", Name("b", 44))])
    conclusion = bind_lq(
        parse_liquid("a > 0 && b > 0 && c > 0"), [("a", Name("a", 43)), ("b", Name("b", 44)), ("c", Name("c", 45))]
    )
    c_gt_0 = bind_lq(parse_liquid("c > 0"), [("c", Name("c", 45))])

    # forall x: (a > 0 && b > 0) => (a > 0 && b > 0 && c > 0)
    c = Implication(x_name, t_int, premise, LiquidConstraint(conclusion))
    r = simplify_constraint(c)

    # Should simplify to: forall x: (a > 0 && b > 0) => c > 0
    expected = Implication(x_name, t_int, premise, LiquidConstraint(c_gt_0))
    assert r == expected, f"Got {r}, expected {expected}"


def test_simplify_no_redundancy():
    """Simplifies implications with no redundant conjuncts should remain unchanged."""
    x_name = Name("x", 42)
    a_gt_0 = bind_lq(parse_liquid("a > 0"), [("a", Name("a", 43))])
    b_gt_0 = bind_lq(parse_liquid("b > 0"), [("b", Name("b", 44))])

    # forall x: a > 0 => b > 0 (no redundancy)
    c = Implication(x_name, t_int, a_gt_0, LiquidConstraint(b_gt_0))
    r = simplify_constraint(c)

    # Should remain: forall x: a > 0 => b > 0
    expected = Implication(x_name, t_int, a_gt_0, LiquidConstraint(b_gt_0))
    assert r == expected, f"Got {r}, expected {expected}"


# ---------------------------------------------------------------------------
# Tests for generalised equality elimination
# ---------------------------------------------------------------------------


def test_simplify_variable_equality_elimination():
    """forall a:Int, a == 1 -> a > 0  simplifies to  true (1 > 0 folded)."""
    a_name = Name("a", 10)
    pred = bind_lq(parse_liquid("a == 1"), [("a", a_name)])
    concl = bind_lq(parse_liquid("a > 0"), [("a", a_name)])

    c = Implication(a_name, t_int, pred, LiquidConstraint(concl))
    r = simplify_constraint(c)

    # a → 1, then 1 > 0 folds to true
    assert r == LiquidConstraint(LiquidLiteralBool(True)), f"Got {r}"


def test_simplify_variable_equality_eliminates_var():
    """forall a:Int, a == b -> a > 0  simplifies to  b > 0."""
    a_name = Name("a", 10)
    b_name = Name("b", 11)
    pred = bind_lq(parse_liquid("a == b"), [("a", a_name), ("b", b_name)])
    concl = bind_lq(parse_liquid("a > 0"), [("a", a_name)])

    c = Implication(a_name, t_int, pred, LiquidConstraint(concl))
    r = simplify_constraint(c)

    expected_concl = bind_lq(parse_liquid("b > 0"), [("b", b_name)])
    assert r == LiquidConstraint(expected_concl), f"Got {r}"


def test_simplify_variable_equality_reversed():
    """forall a:Int, 1 == a -> a > 0  simplifies to  true (1 > 0 folded)."""
    a_name = Name("a", 10)
    pred = bind_lq(parse_liquid("1 == a"), [("a", a_name)])
    concl = bind_lq(parse_liquid("a > 0"), [("a", a_name)])

    c = Implication(a_name, t_int, pred, LiquidConstraint(concl))
    r = simplify_constraint(c)

    assert r == LiquidConstraint(LiquidLiteralBool(True)), f"Got {r}"


def test_simplify_variable_equality_in_conjunction():
    """forall a:Int, (a > 0) && (a == 5) -> a > 3  eliminates a and
    keeps remaining predicate, then constant-folds."""
    a_name = Name("a", 10)
    pred = bind_lq(parse_liquid("a > 0 && a == 5"), [("a", a_name)])
    concl = bind_lq(parse_liquid("a > 3"), [("a", a_name)])

    c = Implication(a_name, t_int, pred, LiquidConstraint(concl))
    r = simplify_constraint_fixpoint(c)

    # a → 5, remaining pred becomes 5 > 0 → true, conclusion 5 > 3 → true
    assert r == LiquidConstraint(LiquidLiteralBool(True)), f"Got {r}"


def test_simplify_function_application_equality():
    """forall x:K, size(x) == 3 -> size(x) > 0  simplifies to  true (3 > 0 folded)."""
    x_name = Name("x", 20)
    size_name = Name("size", 0)

    pred = bind_lq(parse_liquid("size(x) == 3"), [("size", size_name), ("x", x_name)])
    concl = bind_lq(parse_liquid("size(x) > 0"), [("size", size_name), ("x", x_name)])

    k_type = TypeConstructor(Name("K", 0))
    c = Implication(x_name, k_type, pred, LiquidConstraint(concl))
    r = simplify_constraint(c)

    # size(x) → 3, then 3 > 0 folds to true
    assert r == LiquidConstraint(LiquidLiteralBool(True)), f"Got {r}"


def test_simplify_function_application_equality_no_fold():
    """forall x:K, size(x) == n -> size(x) > 0  simplifies to  n > 0."""
    x_name = Name("x", 20)
    n_name = Name("n", 21)
    size_name = Name("size", 0)

    pred = bind_lq(parse_liquid("size(x) == n"), [("size", size_name), ("x", x_name), ("n", n_name)])
    concl = bind_lq(parse_liquid("size(x) > 0"), [("size", size_name), ("x", x_name)])

    k_type = TypeConstructor(Name("K", 0))
    c = Implication(x_name, k_type, pred, LiquidConstraint(concl))
    r = simplify_constraint(c)

    expected_concl = bind_lq(parse_liquid("n > 0"), [("n", n_name)])
    assert r == LiquidConstraint(expected_concl), f"Got {r}"


def test_simplify_nested_equality_elimination():
    """Chained equality elimination through multiple binders."""
    a_name = Name("a", 10)
    b_name = Name("b", 11)

    pred_a = bind_lq(parse_liquid("a == 1"), [("a", a_name)])
    pred_b = bind_lq(parse_liquid("b == a + 1"), [("b", b_name), ("a", a_name)])
    concl = bind_lq(parse_liquid("b > 0"), [("b", b_name)])

    inner = Implication(b_name, t_int, pred_b, LiquidConstraint(concl))
    c = Implication(a_name, t_int, pred_a, inner)
    r = simplify_constraint_fixpoint(c)

    # a → 1, b → 1 + 1 = 2, so b > 0 → 2 > 0 → true
    assert r == LiquidConstraint(LiquidLiteralBool(True)), f"Got {r}"


# ---------------------------------------------------------------------------
# Tests for constant folding
# ---------------------------------------------------------------------------


def test_constant_fold_int_addition():
    x = parse_liquid("1 + 1")
    r = simplify_expr(x)
    assert r == LiquidLiteralInt(2), f"Got {r}"


def test_constant_fold_int_subtraction():
    x = parse_liquid("5 - 3")
    r = simplify_expr(x)
    assert r == LiquidLiteralInt(2), f"Got {r}"


def test_constant_fold_int_multiplication():
    x = parse_liquid("3 * 4")
    r = simplify_expr(x)
    assert r == LiquidLiteralInt(12), f"Got {r}"


def test_constant_fold_comparison_gt():
    x = parse_liquid("5 > 3")
    r = simplify_expr(x)
    assert r == LiquidLiteralBool(True), f"Got {r}"


def test_constant_fold_comparison_lt():
    x = parse_liquid("5 < 3")
    r = simplify_expr(x)
    assert r == LiquidLiteralBool(False), f"Got {r}"


def test_constant_fold_comparison_geq():
    x = parse_liquid("3 >= 3")
    r = simplify_expr(x)
    assert r == LiquidLiteralBool(True), f"Got {r}"


def test_constant_fold_comparison_leq():
    x = parse_liquid("2 <= 3")
    r = simplify_expr(x)
    assert r == LiquidLiteralBool(True), f"Got {r}"


def test_constant_fold_neq():
    x = parse_liquid("1 != 2")
    r = simplify_expr(x)
    assert r == LiquidLiteralBool(True), f"Got {r}"


def test_algebraic_identity_add_zero():
    x = parse_liquid("a + 0")
    r = simplify_expr(x)
    assert r == LiquidVar(Name("a")), f"Got {r}"


def test_algebraic_identity_mul_one():
    x = parse_liquid("a * 1")
    r = simplify_expr(x)
    assert r == LiquidVar(Name("a")), f"Got {r}"


def test_algebraic_identity_mul_zero():
    x = parse_liquid("a * 0")
    r = simplify_expr(x)
    assert r == LiquidLiteralInt(0), f"Got {r}"


def test_algebraic_identity_sub_self():
    a_name = Name("a", 5)
    a = LiquidVar(a_name)
    from aeon.core.liquid import LiquidApp

    expr = LiquidApp(Name("-", 0), [a, a])
    r = simplify_expr(expr)
    assert r == LiquidLiteralInt(0), f"Got {r}"


# ---------------------------------------------------------------------------
# Tests for fixpoint with constant folding + equality elimination
# ---------------------------------------------------------------------------


def test_fixpoint_equality_then_constant_fold():
    """forall a:Int, a == 1 -> a + 1 > 0  simplifies to  2 > 0  then to  true."""
    a_name = Name("a", 10)
    pred = bind_lq(parse_liquid("a == 1"), [("a", a_name)])
    concl = bind_lq(parse_liquid("a + 1 > 0"), [("a", a_name)])

    c = Implication(a_name, t_int, pred, LiquidConstraint(concl))
    r = simplify_constraint_fixpoint(c)

    # a → 1, so a + 1 → 1 + 1 → 2, then 2 > 0 → true
    assert r == LiquidConstraint(LiquidLiteralBool(True)), f"Got {r}"


def test_fixpoint_extensibility():
    """Extra passes can be injected into the fixpoint loop."""
    a_name = Name("a", 10)
    pred = bind_lq(parse_liquid("a == 1"), [("a", a_name)])
    concl = bind_lq(parse_liquid("a > 0"), [("a", a_name)])
    c = Implication(a_name, t_int, pred, LiquidConstraint(concl))

    call_count = [0]

    def counting_pass(c):
        call_count[0] += 1
        return c

    simplify_constraint_fixpoint(c, extra_passes=[counting_pass])
    assert call_count[0] > 0, "Extra pass was never called"


# ---------------------------------------------------------------------------
# Tests for error-message goal extraction and trivial-refinement printing
# ---------------------------------------------------------------------------


def test_constraint_goal_extracts_conclusion():
    """constraint_goal digs through binders/premises to the final goal."""
    from aeon.verification.helpers import constraint_goal

    a_name = Name("a", 10)
    pred = bind_lq(parse_liquid("a > 0"), [("a", a_name)])
    concl = bind_lq(parse_liquid("a > 5"), [("a", a_name)])
    c = Implication(a_name, t_int, pred, LiquidConstraint(concl))

    assert constraint_goal(c) == concl


def test_pretty_print_omits_trivial_true_refinement():
    """A binder with a trivial `true` refinement prints without `| true`."""
    from aeon.verification.helpers import pretty_print_constraint

    a_name = Name("a", 10)
    # forall a:Int (with trivial `true` premise) => a > 5
    concl = bind_lq(parse_liquid("a > 5"), [("a", a_name)])
    c = Implication(a_name, t_int, LiquidLiteralBool(True), LiquidConstraint(concl))

    out = pretty_print_constraint(c)
    assert "| true" not in out, out
    # The binder itself is still shown.
    assert "∀a" in out, out
