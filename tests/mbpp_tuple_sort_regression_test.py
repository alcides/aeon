"""The exact constructor/selector candidate from the MBPP 307 crash."""

from pathlib import Path

import pytest

from aeon.core.substitutions import substitution
from aeon.core.terms import Application, Literal, Var
from aeon.core.types import t_bool, t_int, t_string, top
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.identification import get_holes_info, incomplete_functions_and_holes
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.typeinfer import check_type


@pytest.mark.parametrize("valid", [True, False])
def test_mbpp_307_constructor_and_opaque_selector_keep_their_sorts(valid):
    source = Path(__file__).resolve().parents[1] / "examples/MBPP/mbpp_307.ae"
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 5, no_main=True))
    assert driver.parse(aeon_code=source.read_text()) == []
    # Warm a second session with an incompatible definition of the same type.
    foreign = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 0, no_main=True))
    assert foreign.parse(aeon_code="inductive Tuple | mk (a0:Int) : Tuple\ndef n:Int := 0;") == []
    with driver.session.activate():
        targets = incomplete_functions_and_holes(driver.typing_ctx, driver.core)
        holes = get_holes_info(driver.typing_ctx, driver.core, top, targets, refined_types=True)
        hole, (_, scope) = next(iter(holes.items()))
        names = {name.name: name for name, _ in scope.vars()}
        candidate = Var(names["Tuple_mk"])
        tail = Application(Var(names["Tuple_mk_a2"]), Var(names["tuplex"]))
        for argument in (
            Literal("", t_string),
            Literal(-2, t_int),
            tail,
            Literal(True, t_bool) if valid else Literal(1, t_int),
        ):
            candidate = Application(candidate, argument)
        assert check_type(driver.typing_ctx, substitution(driver.core, candidate, hole)) is valid
