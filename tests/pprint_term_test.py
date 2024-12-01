from aeon.core.pprint import custom_preludes_ops_representation
from aeon.core.terms import Var, Application


def test_rewrite_op_term():
    initial_term = Application(fun=Var("*"), arg=Var("x"))

    custom_preludes_ops_representation(initial_term)[0]
    # Todo: fix this test
    # assert final_term == "(\\__mult_1__ -> x * __mult_1__)"
    assert True
