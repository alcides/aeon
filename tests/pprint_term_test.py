from aeon.core.pprint import custom_preludes_ops_representation
from aeon.core.terms import Var, Application
from aeon.utils.name import Name


def test_partial_operator_application_is_eta_expanded():
    # (* x) is a partially applied operator and must render as a lambda.
    term = Application(fun=Var(Name("*", 0)), arg=Var(Name("x", 0)))
    result, _ = custom_preludes_ops_representation(term)
    assert result == "(fun __mul_1__ => x * __mul_1__)"


def test_full_operator_application_renders_infix_in_source_order():
    # ((>= a) b) must render as (a >= b), with operands in source order.
    term = Application(
        fun=Application(fun=Var(Name(">=", 0)), arg=Var(Name("a", 0))),
        arg=Var(Name("b", 0)),
    )
    result, _ = custom_preludes_ops_representation(term)
    assert result == "(a >= b)"


def test_unary_operator_application():
    # (! b) is a fully applied unary operator.
    term = Application(fun=Var(Name("!", 0)), arg=Var(Name("b", 0)))
    result, _ = custom_preludes_ops_representation(term)
    assert result == "(!b)"
