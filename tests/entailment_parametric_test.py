"""Parametric ADT binders must keep their constructor type in VCs (not Int)."""

from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt, LiquidVar
from aeon.core.types import RefinedType, TypeConstructor, t_int, top
from aeon.typechecking.context import TypingContext, VariableBinder
from aeon.typechecking.entailment import entailment_context
from aeon.utils.name import Name
from aeon.verification.vcs import Implication, LiquidConstraint


def test_parametric_list_binder_keeps_list_int_sort():
    list_int = TypeConstructor(Name("List", 0), [t_int])
    xs = Name("xs", 0)
    ctx = TypingContext([VariableBinder(xs, list_int)])
    goal = LiquidConstraint(LiquidLiteralBool(True))
    vc = entailment_context(ctx, goal)
    assert isinstance(vc, Implication)
    assert vc.name == xs
    assert isinstance(vc.base, TypeConstructor)
    assert vc.base.name.name == "List"
    assert vc.base.args == [t_int]


def test_nullary_constructor_binder_unchanged():
    x = Name("x", 0)
    ctx = TypingContext([VariableBinder(x, t_int)])
    goal = LiquidConstraint(LiquidLiteralBool(True))
    vc = entailment_context(ctx, goal)
    assert isinstance(vc, Implication)
    assert vc.base == t_int


def test_top_runtime_binding_adds_no_assumption_and_preserves_refinements():
    x, binder, measured = Name("x", 0), Name("value", 0), Name("measured", 0)
    predicate = LiquidApp(Name(">", 0), [LiquidVar(binder), LiquidLiteralInt(0)])
    ctx = TypingContext([VariableBinder(x, RefinedType(binder, t_int, predicate)), VariableBinder(measured, top)])
    goal = LiquidConstraint(LiquidLiteralBool(False))
    vc = entailment_context(ctx, goal)
    assert isinstance(vc, Implication)
    assert vc.name == x and vc.base == t_int
    assert vc.pred == LiquidApp(Name(">", 0), [LiquidVar(x), LiquidLiteralInt(0)])
    assert vc.seq is goal  # Even a false obligation must remain unchanged.
