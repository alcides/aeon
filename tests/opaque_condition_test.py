"""Executable Boolean guards need not be expressible as liquid predicates."""

from aeon.core.terms import Abstraction, Application, If, Literal, Var
from aeon.core.types import AbstractionType, t_bool, t_int
from aeon.core.substitutions import liquefy
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name


def guard(base=t_bool):
    x, f, apply = Name("x", 501), Name("f", 502), Name("apply", 503)
    arrow = AbstractionType(x, base, base)
    ctx = TypingContext().with_var(apply, AbstractionType(f, arrow, base))
    return ctx, Application(Var(apply), Abstraction(x, Var(x)))


def test_opaque_boolean_guard_checks_both_branches():
    ctx, condition = guard()
    assert liquefy(condition) is None
    assert check_type(ctx, If(condition, Literal(1, t_int), Literal(2, t_int)), t_int)


def test_opaque_guard_does_not_hide_bad_branch():
    ctx, condition = guard()
    assert not check_type(ctx, If(condition, Literal(1, t_int), Literal(False, t_bool)), t_int)


def test_opaque_non_boolean_guard_is_rejected():
    ctx, condition = guard(t_int)
    assert not check_type(ctx, If(condition, Literal(1, t_int), Literal(2, t_int)), t_int)


def test_opaque_guard_synthesizes_inside_a_let():
    from aeon.core.terms import Let

    ctx, condition = guard()
    result = Name("result", 504)
    expression = Let(result, If(condition, Literal(1, t_int), Literal(2, t_int)), Var(result))
    assert check_type(ctx, expression, t_int)
