"""The main knapsack returns a fixed Boolean array and rejects overweight candidates."""

from contextlib import contextmanager
from pathlib import Path

import pytest

from aeon.core.terms import Literal
from aeon.core.types import RefinedType, top, t_bool
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.api import InvalidIndividualException
from aeon.synthesis.identification import get_holes_info
from aeon.synthesis.program_specifications import ProgramSpecifications
from aeon.synthesis.uis.api import SilentSynthesisUI
from tests.knapsack_50_test import _items


EXAMPLES = Path(__file__).resolve().parents[1] / "examples/synthesis/puzzle"


@contextmanager
def problem(filename="knapsack_50.ae"):
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0, strict_decidable=True))
    assert not list(driver.parse(filename=str(EXAMPLES / filename)))
    assert driver.has_synth()
    with driver.session.activate():
        [(function, [hole])] = driver.incomplete_functions
        assert hole.name == "solution"
        goal, _ = get_holes_info(driver.typing_ctx, driver.core, top, driver.incomplete_functions, refined_types=True)[
            hole
        ]
        assert isinstance(goal, RefinedType)
        assert goal.type.name.name == "Array" and goal.type.args == [t_bool]
        with ProgramSpecifications(
            driver.typing_ctx,
            driver.evaluation_ctx,
            driver.core,
            driver.incomplete_functions,
            driver.metadata,
            pooled=False,
        ) as specs:
            yield driver, specs, hole, goal.type


@pytest.mark.parametrize("filename", ["knapsack_50.ae", "knapsack_50_array.ae"])
@pytest.mark.parametrize("selected", [set(), {4, 6, 9, 11, 16, 19, 25, 27, 31, 32, 34, 40, 41, 42, 45, 46}])
def test_feasible_decisions_keep_item_order_and_score(filename, selected):
    decisions = [i in selected for i in range(50)]
    weight = sum(w for (_, w), used in zip(_items(), decisions) if used)
    value = sum(v for (v, _), used in zip(_items(), decisions) if used)
    assert weight == (100 if selected else 0)
    with problem(filename) as (driver, specs, hole, array_type):
        candidate = specs.candidate({hole: Literal(decisions, array_type)})
        assert specs.validate(candidate)
        assert specs.evaluate(candidate) == [float(value)]
        driver.core = specs.replace(candidate)
        assert driver.run() == decisions
        assert any(goal.kind == "require" for goal in specs.checks)
        [objective] = [goal for goal in specs.goals if goal.kind != "require"]
        assert not objective.minimize


def test_overweight_selection_is_rejected_before_scoring():
    assert sum(w for _, w in _items()) > 100
    with problem() as (_, specs, hole, array_type):
        candidate = specs.candidate({hole: Literal([True] * 50, array_type)})
        assert not specs.validate(candidate)
        with pytest.raises(InvalidIndividualException, match="@require"):
            specs.evaluate(candidate)


@pytest.mark.parametrize("values", [[False] * 49, [False] * 51, [0] * 50])
def test_length_and_boolean_element_types_are_enforced(values):
    with problem() as (_, specs, hole, array_type):
        assert not specs.validate(specs.candidate({hole: Literal(values, array_type)}))
