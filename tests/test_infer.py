from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
import pytest

from aeon.typing.context import EmptyContext, VariableBinder
from aeon.typing.typeinfer import InferenceError, synth_type
from aeon.typing.subtyping import is_subtype, is_subtype
from aeon.core.types import AbstractionType, RefinedType, t_int, t_bool
from aeon.core.terms import Literal, Var, Application, Abstraction

from aeon.utils.ast_helpers import i1

x = Var(name="x")
y = Var(name="y")
z = Var(name="z")
f = Var(name="f")
f_x = Application(f, x)
la = Abstraction("x", t_bool, x)
app_la_x = Application(la, x)

int_to_int = AbstractionType("x", t_int, t_int)

ctx_empty = EmptyContext()
ctx_x_int = VariableBinder(ctx_empty, "x", t_int)
ctx_y_bool = VariableBinder(ctx_empty, "y", t_bool)
ctx_x_f = VariableBinder(ctx_x_int, "f", int_to_int)


def test_one_is_int():
    assert is_subtype(ctx_empty, synth_type(ctx_empty, i1), t_int)


def test_x_is_int():
    assert is_subtype(ctx_x_int, synth_type(ctx_x_int, x), t_int)


def test_y_is_bool():
    assert is_subtype(ctx_y_bool, synth_type(ctx_y_bool, y), t_bool)


def test_no_z():
    with pytest.raises(InferenceError):
        assert synth_type(ctx_x_int, z)


def test_f_is_int_to_int():
    assert is_subtype(ctx_x_f, synth_type(ctx_x_f, f), int_to_int)


def test_f_x_is_int():
    assert is_subtype(ctx_x_f, synth_type(ctx_x_f, f_x), t_int)


def test_la_x_is_int():
    assert is_subtype(ctx_empty, synth_type(ctx_x_f, app_la_x), t_bool)
