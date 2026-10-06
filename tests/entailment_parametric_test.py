"""Parametric ADT binders must keep their constructor type in VCs (not Int)."""

from aeon.core.liquid import LiquidLiteralBool
from aeon.core.types import TypeConstructor, t_int
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
