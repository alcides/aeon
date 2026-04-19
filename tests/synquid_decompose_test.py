from aeon.core.parser import parse_type
from aeon.core.terms import Literal
from aeon.core.types import RefinedType, TypeConstructor
from aeon.synthesis.modules.synquid.decompose import uncurry
from aeon.synthesis.modules.synquid.modular import application_subgoal_types, check_hole_term
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


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


def test_check_hole_term_int_literal():
    ctx = TypingContext()
    int_t = TypeConstructor(Name("Int", 0), [])
    lit = Literal(42, int_t)
    assert check_hole_term(ctx, lit, int_t)
