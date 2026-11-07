"""Invalid polymorphic applications must backtrack without losing valid ones."""

import pytest

from aeon.compilation.session import CompilationSession
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.types import AbstractionType, Kind, RefinedType, TypeConstructor, t_bool, t_int
from aeon.synthesis.modules.synquid.constraints import ConstraintState
from aeon.synthesis.modules.synquid.engine import synthes_memory
from aeon.synthesis.modules.synquid.solver import Status
from aeon.typechecking.context import TypeConstructorBinder
from aeon.typechecking.typeinfer import check_type
from aeon.utils.ctx_helpers import built_std_context
from tests.synquid_round_trip_test import name, parse_type


@pytest.fixture(autouse=True)
def compilation_session():
    with CompilationSession().activate():
        yield


@pytest.mark.parametrize("reverse", [False, True])
def test_refined_base_variable_rejects_function_shape(reverse):
    state = ConstraintState(built_std_context())
    alpha = state.fresh_variable(Kind.BASE)
    refined = RefinedType(name("v"), alpha, LiquidLiteralBool(True))
    function = AbstractionType(name("x"), t_int, t_bool)
    state.subtype(*((function, refined) if reverse else (refined, function)))
    assert state.solve() == Status.INVALID


def test_failed_function_instantiation_does_not_poison_sibling():
    state = ConstraintState(built_std_context())
    alpha = state.fresh_variable(Kind.BASE)
    refined = RefinedType(name("v"), alpha, LiquidLiteralBool(True))
    bad = state.fork()
    bad.subtype(refined, AbstractionType(name("x"), t_int, t_bool))
    assert bad.solve() == Status.INVALID
    good = state.fork()
    good.subtype(refined, t_int)
    assert good.solve() == Status.VALID
    assert state.unresolved(alpha)
    assert not good.unresolved(alpha)


def test_star_variable_accepts_function_shape():
    state = ConstraintState(built_std_context())
    alpha = state.fresh_variable(Kind.STAR)
    function = AbstractionType(name("x"), t_int, t_bool)
    state.subtype(alpha, function)
    assert state.solve() == Status.VALID
    assert isinstance(state.resolve(alpha), AbstractionType)


def test_equality_search_skips_function_valued_array_accessor():
    # The Game of Life crash compared equality itself with Array.got_value.
    # This small component grammar exercises the same polymorphic application.
    ctx = built_std_context()
    ctx.entries.append(TypeConstructorBinder(name("Seq"), [name("a")]))
    accessor = parse_type("forall a:B, (g:Seq {v:a | true}) -> {v:a | true}")
    ctx = ctx.with_var(name("accessor"), accessor)
    ctx = ctx.with_var(name("xs"), TypeConstructor(name("Seq"), [t_int]))
    terms = list(
        synthes_memory(ctx, 1, t_bool, lambda n: n.name not in {"==", "accessor", "xs"}, {}, conditionals=False)
    )
    assert terms
    assert any(check_type(ctx, term, t_bool) for term in terms)
