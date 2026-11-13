"""Each fitness evaluation owns a copy of a stable training fixture."""

import random
from unittest.mock import Mock

import psb2

from aeon.bindings.psb2 import training_data
from aeon.errors import LinearityError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


def test_fixture_is_lazy_and_returns_independent_nested_snapshots(monkeypatch):
    cases = [[[[1, 2]], [3]], [[[4, 5]], [9]]]
    fetch = Mock(return_value=(cases, []))
    monkeypatch.setattr(psb2, "fetch_examples", fetch)
    fixture = training_data("vector", 2, 0)
    fetch.assert_not_called()
    first = fixture(None)
    first[0][0][0][0] = 99
    first[0][1][0] = 42
    assert fixture(None) == cases
    assert cases[0][0][0][0] == 1
    fetch.assert_called_once_with("path/to/PSB2/datasets/", "vector", 2, 0, format="lists", seed=0)


def test_fixtures_agree_across_workers_without_resetting_search_rng(monkeypatch):
    def fetch(*args, seed, **kwargs):
        random.seed(seed)
        return ([[[random.randrange(1000000)], [0]]], [])

    monkeypatch.setattr(psb2, "fetch_examples", fetch)
    before = random.getstate()
    assert training_data("a", 1, 0)(None) == training_data("a", 1, 0)(None)
    assert random.getstate() == before


def compile_source(source):
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0))
    return driver, list(driver.parse(aeon_code="open PSB2\n" + source))


def test_fixture_can_supply_multiple_owned_training_values(monkeypatch):
    fetch = Mock(return_value=([[[5], [9]], [[7], [11]]], []))
    monkeypatch.setattr(psb2, "fetch_examples", fetch)
    driver, errors = compile_source("""
def cases:TrainingCases := training_data "test" 2 0;
def score (1 data:TrainData):Int :=
    with_lists data (fun inputs => fun outputs => native "inputs[0][0] + outputs[0]");
def main (_:Int):Int := score (fresh_train_data cases) + score (fresh_train_data cases);
""")
    assert not errors, errors
    assert driver.run() == 28
    fetch.assert_called_once()


def test_training_owner_cannot_be_projected_twice():
    _, errors = compile_source("""
def bad (1 data:TrainData):Int :=
    let 1 first := get_input_list (unpack_train_data data) in
    let 1 second := get_output_list (unpack_train_data data) in
    let _ := Array.dispose first in
    let _ := Array.dispose second in 0;
def main (_:Int):Int := 0;
""")
    assert any(isinstance(error, LinearityError) for error in errors), errors
