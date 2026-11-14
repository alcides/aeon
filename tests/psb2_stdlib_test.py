"""Exercise all PSB2 references, typed dataset bridges, and contracts offline."""

import json
from pathlib import Path

import pytest

from aeon.backend.python_export import export_function
from aeon.bindings.lists import from_iterable, to_list
from aeon.bindings.psb2 import errors
from aeon.core.types import refined_to_unrefined_type, t_unit, top
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.identification import get_holes_info
from aeon.synthesis.uis.api import SilentSynthesisUI

setup_logger()

ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / "examples/benchmarks/psb2"
CASES = json.loads((SUITE / "conformance.json").read_text())
ALIASES = {
    "coin-sums": "coin_sum",
    "fizz-buzz": "fizzbuzz",
    "middle-character": "middle_char",
    "shopping-list": "shopping",
}


def compile_source(source=None, path=None):
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0, no_main=True))
    failures = driver.parse(aeon_code=source, filename=str(path) if path else None)
    assert not failures, (path, failures)
    return driver


@pytest.fixture(scope="module")
def references():
    result = {}
    for problem in CASES:
        name = ALIASES.get(problem, problem.replace("-", "_"))
        driver = compile_source(path=SUITE / "solved" / f"{name}.ae")
        namespace = {}
        exec(driver.export(name), namespace)
        result[problem] = namespace[name]
    return result


@pytest.mark.parametrize("problem", CASES)
def test_every_reference_matches_conformance_cases(problem, references):
    scores = errors(problem, CASES[problem], references[problem])
    assert len(scores) == len(CASES[problem])
    assert scores == pytest.approx([0.0] * len(scores), abs=1e-7)


@pytest.mark.parametrize(
    "path", sorted(p for p in SUITE.rglob("*.ae") if "solved" not in p.parts), ids=lambda p: str(p.relative_to(SUITE))
)
def test_every_fitness_bridge_calls_the_curried_reference_with_typed_data(path, references):
    source = path.read_text()
    problem = source.split("# PSB2: ")[1].splitlines()[0]
    driver = compile_source(path=path)
    namespace = {}
    # Export the scoring binding without synthesizing the unrelated target hole.
    with driver.session.activate():
        exec(export_function(driver.core, "score"), namespace)
    scores = namespace["score"](lambda _: CASES[problem])(references[problem])
    assert scores == pytest.approx([0.0] * len(CASES[problem]), abs=1e-7)
    assert_hidden_ingredients(driver, path)


def assert_hidden_ingredients(driver, path):
    with driver.session.activate():
        holes = get_holes_info(driver.typing_ctx, driver.core, top, [], refined_types=True)
        assert len(holes) == 1
        _, context = next(iter(holes.values()))
        visible = {name.name: refined_to_unrefined_type(ty) for name, ty in context.concrete_vars()}
    for name in ("train", "score", "PSB2Fitness_cases"):
        assert visible[name] == t_unit
    assert visible["List_map"] != t_unit
    assert visible["List_filter"] != t_unit
    assert visible["String_characters"] != t_unit
    if path.stem == "gcd":
        assert visible["Math_gcd"] == t_unit
    for name in ("dice_game", "square_digit_unsafe"):
        if name in visible:
            assert visible[name] == t_unit


def test_nested_output_errors_compare_elements_not_just_sums():
    def wrong(_):
        return from_iterable([from_iterable([0, 2]), from_iterable([3])])

    assert errors("cut-vector", [[[[1, 1, 3]], [[1, 1], [3]]]], wrong) == [2.0]


def test_float_columns_and_fractional_errors_are_preserved():
    seen = []

    def candidate(prices):
        seen.append(to_list(prices))
        return lambda discounts: 1.25

    assert errors("shopping-list", [[[[1.5], [25.5]], [1.5]]], candidate) == [0.25]
    assert seen == [[1.5]]


@pytest.mark.parametrize("value", [float("nan"), float("inf"), True, "0"])
def test_invalid_numeric_candidate_results_are_rejected(value):
    with pytest.raises(ValueError, match="finite PSB2 numeric"):
        errors("gcd", [[[2, 4], [2]]], lambda _: lambda _: value)
