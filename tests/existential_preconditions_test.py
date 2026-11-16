"""A result's existential facts cannot justify its own call preconditions."""

import pytest

from aeon.core.bind import bind_ids
from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt, LiquidVar
from aeon.core.terms import Application, If, Let, Literal, Var
from aeon.core.types import AbstractionType, RefinedType, t_bool, t_int
from aeon.elaboration.context import build_typing_context
from aeon.prelude.prelude import typing_vars
from aeon.sugar.lowering import lower_to_core_context
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name


@pytest.mark.parametrize("position", ["curried_argument", "checked_guard", "inferred_guard"])
def test_preconditions_cannot_assume_an_impossible_result(position):
    ctx = lower_to_core_context(build_typing_context(typing_vars))
    x, b, guard, consume = (Name(name) for name in ["x", "b", "guard", "consume"])
    positive = RefinedType(x, t_int, LiquidApp(Name(">"), [LiquidVar(x), LiquidLiteralInt(0)]))
    impossible = RefinedType(b, t_bool, LiquidLiteralBool(False))
    ctx = ctx.with_var(guard, AbstractionType(x, positive, impossible))
    invalid_call = Application(Var(guard), Literal(0, t_int))

    if position == "curried_argument":
        ctx = ctx.with_var(consume, AbstractionType(b, t_bool, AbstractionType(x, t_int, t_int)))
        term = Application(Application(Var(consume), invalid_call), Literal(1, t_int))
    else:
        ctx = ctx.with_var(consume, AbstractionType(b, t_bool, t_bool))
        condition = Application(Var(consume), invalid_call)
        term = If(condition, Literal(1, t_int), Literal(2, t_int))
        if position == "inferred_guard":
            result = Name("result")
            term = Let(result, term, Var(result))

    ctx, term = bind_ids(ctx, term)
    assert not check_type(ctx, term)
