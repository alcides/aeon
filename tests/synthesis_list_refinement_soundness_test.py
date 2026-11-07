"""The length-ten list regression exercises the shared synthesis validator."""

import pytest

from aeon.core.terms import Abstraction, Application, Hole, Literal, RefinementApplication, TypeApplication, Var
from aeon.core.types import t_bool, t_int, top
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.entrypoint import make_program, make_validator
from aeon.synthesis.identification import get_holes_info
from aeon.synthesis.tactics.builtin import tactic_apply_question
from aeon.synthesis.tactics.state import TacticState
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.name import Name


@pytest.fixture
def list_problem():
    driver = AeonDriver(AeonConfig("tactics", SilentSynthesisUI(), 1))
    assert not list(driver.parse(aeon_code="open List\ndef ten : {xs:(List Int) | List.size xs = 10} := ?body;"))
    with driver.session.activate():
        holes = get_holes_info(driver.typing_ctx, driver.core, top, [], refined_types=True)
        hole, (goal, ctx) = next((name, info) for name, info in holes.items() if name.name == "body")
        names = {name.name: name for name, _ in ctx.concrete_vars()}
        validate = make_validator(driver.typing_ctx, make_program(driver.core, hole), driver.metadata)
        yield hole, goal, ctx, names, validate


def test_apply_cannot_close_length_ten_with_bare_nil(list_problem):
    hole, goal, ctx, names, validate = list_problem
    assert not validate(Var(names["List_nil"]))
    assert not validate(TypeApplication(Var(names["List_nil"]), t_int))
    assert tactic_apply_question(TacticState(ctx, Hole(hole), goal), hole) is None


@pytest.mark.parametrize("length", [0, 9, 10, 11])
def test_shared_validator_checks_instantiated_list_length(list_problem, length):
    _, _, _, names, validate = list_problem

    def constructor(name):
        return RefinementApplication(
            TypeApplication(Var(names[name]), t_int),
            Abstraction(Name("element"), Literal(True, t_bool)),
        )

    term = constructor("List_nil")
    for _ in range(length):
        term = Application(Application(constructor("List_cons"), Literal(0, t_int)), term)
    assert validate(term) is (length == 10)
