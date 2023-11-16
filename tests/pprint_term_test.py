from aeon.core.terms import Var, Application, Abstraction
from aeon.core.pprint import replace_application_with_abstraction, custom_preludes_ops_representation


def test_replace():
    initial_term = Application(fun=Var("*"), arg=Var("x"))

    final_term = replace_application_with_abstraction(initial_term)[0]

    assert final_term == Abstraction(
        "__mult_1__", Application(arg=Var("__mult_1__"), fun=Application(fun=Var("*"), arg=Var("x")))
    )


def test_rewrite_op_term():
    initial_term = Application(fun=Var("*"), arg=Var("x"))

    final_term = custom_preludes_ops_representation(initial_term)[0]

    assert final_term == "(\\__mult_1__ -> x * __mult_1__)"
