"""PSB2 contracts reject invalid domains and malformed candidate results."""

import re
from pathlib import Path

import pytest

from aeon.bindings.psb2 import errors
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SilentSynthesisUI

setup_logger()

SUITE = Path(__file__).resolve().parents[1] / "examples/benchmarks/psb2/annotations/multi_objective"


def target_source(task):
    source = (SUITE / f"{task}.ae").read_text()
    start = re.search(r"^def (synth|cut_vector)\b", source, re.MULTILINE)
    assert start
    return "import List\nimport Math\nimport String\n" + source[start.start() :]


def parse(source):
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0, no_main=True))
    return driver.parse(aeon_code=source)


@pytest.mark.parametrize(
    "task,call,valid",
    [
        ("dice_game", "synth 1 1", True),
        ("dice_game", "synth 0 1", False),
        ("dice_game", "synth 1001 1", False),
        ("bouncing_balls", "synth 10.0 5.0 2", True),
        ("bouncing_balls", "synth 0.0 1.0 2", False),
        ("bouncing_balls", "synth 10.0 10.0 2", False),
        ("bouncing_balls", "synth 10.0 5.0 0", False),
        ("coin_sum", "synth 1", True),
        ("coin_sum", "synth 0", False),
        ("coin_sum", "synth 10001", False),
        ("gcd", "synth 1 1", True),
        ("gcd", "synth 0 1", False),
        ("middle_char", 'synth "ab"', True),
        ("middle_char", 'synth ""', False),
        ("mastermind", 'synth "RRRR" "GGGG"', True),
        ("mastermind", 'synth "RRR" "GGGG"', False),
        ("snow_day", "synth 1 15.0 15.0 0.15", True),
        ("snow_day", "synth 1 10.0 2.0 1.1", False),
        ("solve_boolean", 'synth "t|f&f"', True),
        ("solve_boolean", 'synth "t&"', False),
        ("substitution_cipher", 'synth "" "" ""', True),
        ("substitution_cipher", 'synth "ab" "x" "a"', False),
        ("square_digits", "synth (-1)", False),
    ],
)
def test_scalar_and_string_input_contracts(task, call, valid):
    source = target_source(task) + f"\ndef probe : Unit := let value := {call} in unit;"
    assert (not parse(source)) == valid


@pytest.mark.parametrize(
    "task,body,valid",
    [
        ("dice_game", "0.0", True),
        ("dice_game", "1.0", False),
        ("gcd", "0", False),
        ("coin_sum", "[]", False),
        ("coin_sum", "[0, 0, 0, 0]", False),
        ("mastermind", "[0, 4]", True),
        ("mastermind", "[1, 4]", False),
        ("mastermind", "[0, 0, 0]", False),
        ("snow_day", "snow", True),
        ("snow_day", "(-1.0)", False),
        ("shopping", "0.0", True),
        ("shopping", "(-0.1)", False),
        ("vector_distance", "0.0", True),
        ("vector_distance", "1001.0", False),
        ("middle_char", '""', False),
        ("square_digits", '""', False),
    ],
)
def test_candidate_result_contracts(task, body, valid):
    assert (not parse(target_source(task).replace("?hole", body))) == valid


@pytest.mark.parametrize(
    "problem,inputs",
    [
        ("fuel-cost", [[5]]),
        ("luhn", [[0] * 15]),
        ("luhn", [[0] * 15 + [10]]),
        ("shopping-list", [[1.0, 2.0], [10.0]]),
        ("shopping-list", [[1.0], [100.1]]),
        ("vector-distance", [[1.0], [1.0, 2.0]]),
        ("vector-distance", [[100.1], [0.0]]),
        ("cut-vector", [[-1]]),
    ],
)
def test_dataset_boundary_checks_list_predicates_before_calling_candidates(problem, inputs):
    def unexpected(_):
        pytest.fail("invalid dataset rows must not be passed to a refined callback")

    with pytest.raises(ValueError, match="violates.*refinements"):
        errors(problem, [[inputs, [0]]], unexpected)
