from aeon.core.parser import parse_type
from aeon.core.types import RefinedType
from aeon.synthesis.modules.synquid.decompose import uncurry
from aeon.synthesis.modules.synquid.modular import application_subgoal_types


def test_uncurry_preserves_refined_domain():
    ty = parse_type("(x:{v:Int | v > 0}) -> Int")
    params, ret = uncurry(ty)
    assert len(params) == 1
    assert isinstance(params[0], RefinedType)
    assert ret == parse_type("Int")


def test_application_subgoal_types_with_refined_goal():
    fn = parse_type("(x:{v:Int | v > 0}) -> Int")
    goal = parse_type("{w:Int | w >= 0}")
    args = application_subgoal_types(fn, goal)
    assert args is not None
    assert len(args) == 1
    assert isinstance(args[0], RefinedType)
