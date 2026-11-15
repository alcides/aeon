"""Check the maintained MBPP ports, their examples, and synthesis ingredients."""

from __future__ import annotations

import contextlib
import io
import json
from pathlib import Path

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.core.types import t_unit, top, refined_to_unrefined_type
from aeon.synthesis.identification import get_holes_info
from aeon.synthesis.pbt import run_examples

# Registers the custom "TIME" log level that the driver's RecordTime uses.
setup_logger()

MBPP_DIR = Path(__file__).parent.parent / "examples/benchmarks/mbpp"
MBPP_FILES = sorted(MBPP_DIR.glob("mbpp_*.ae"))
EXAMPLE_COUNTS = json.loads((MBPP_DIR / "example-counts.json").read_text())


def test_mbpp_directory_is_populated():
    assert {p.stem for p in MBPP_FILES} == set(EXAMPLE_COUNTS)
    assert len(MBPP_FILES) == 427
    assert sum(EXAMPLE_COUNTS.values()) == 1324


@pytest.mark.parametrize("path", MBPP_FILES, ids=lambda p: p.stem)
def test_mbpp_example_parses_and_typechecks(path: Path):
    cfg = AeonConfig(
        synthesizer="random_search",
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=0,
        no_main=True,
    )
    driver = AeonDriver(cfg)
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
        errors = driver.parse(str(path))
    assert not errors, f"{path.name} failed to typecheck: {errors}"
    assert driver.has_synth(), f"{path.name} has no synthesis hole"
    entries = [entry for entry in driver.metadata.values() if entry.get("examples")]
    assert sum(len(entry["examples"]) for entry in entries) == EXAMPLE_COUNTS[path.stem]
    assert all(goal.kind == "example" for entry in entries for goal in entry.get("goals", []))


@pytest.mark.parametrize(
    "task, hidden",
    [
        (798, {"List_sum"}),
        (792, {"List_length", "List_size", "List_structuralRank"}),
        (596, {"System_getSizeOf"}),
        (106, {"List_append"}),
        (788, {"List_snoc"}),
    ],
)
def test_direct_solutions_are_hidden_without_removing_list_ingredients(task, hidden):
    driver = AeonDriver(AeonConfig("random_search", SilentSynthesisUI(), 0, no_main=True))
    assert not driver.parse(str(MBPP_DIR / f"mbpp_{task}.ae"))
    with driver.session.activate():
        holes = get_holes_info(driver.typing_ctx, driver.core, top, [], refined_types=True)
        assert len(holes) == 1
        _, context = next(iter(holes.values()))
        visible = {n.name: ty for n, ty in context.concrete_vars()}
        assert all(refined_to_unrefined_type(visible[name]) == t_unit for name in hidden)
        if task != 596:
            assert refined_to_unrefined_type(visible["List_foldr"]) != t_unit
            assert refined_to_unrefined_type(visible["List_map"]) != t_unit
            assert refined_to_unrefined_type(visible["List_cons"]) != t_unit


@pytest.mark.parametrize(
    "task, implementation",
    [
        (798, "match arr with | List.nil => 0 | List.cons x rest => x + (_sum rest)"),
        (792, "match input_list with | List.nil => 0 | List.cons x rest => 1 + (count_list rest)"),
        (101, "match arr with | List.nil => 0 | List.cons x rest => if k = 1 then x else kth_element rest (k - 1)"),
        (587, "listx"),
        (
            70,
            "match Input with | List.nil => true | List.cons xs rest => "
            "List.all (fun ys => List.length ys = List.length xs) rest",
        ),
        (
            250,
            "match tup with | List.nil => 0 | List.cons y rest => (if y = x then 1 else 0) + count_X rest x",
        ),
        (
            744,
            "!(List.all (fun item => match item with | Maybe.none => false | Maybe.just value => true) test_tup)",
        ),
        (
            253,
            "match list1 with | List.nil => 0 | List.cons x xs => "
            "(match x with | Value1.asInt n => 1 + count_integer xs "
            "| Value1.asFloat n => count_integer xs | Value1.asString s => count_integer xs)",
        ),
        (
            264,
            "if h_age = 0 then 0.0 else if h_age = 1 then 10.5 else "
            "if h_age = 2 then 21.0 else dog_age (h_age - 1) + 4.0",
        ),
    ],
)
def test_ported_examples_run_with_concrete_implementations(task, implementation):
    source = (MBPP_DIR / f"mbpp_{task}.ae").read_text().replace("?hole", f"({implementation})")
    driver = AeonDriver(AeonConfig("random_search", SilentSynthesisUI(), 0, no_main=True))
    assert not driver.parse(aeon_code=source)
    with driver.session.activate():
        results = run_examples(driver.evaluation_ctx, driver.core, driver.metadata)
    assert len(results) == EXAMPLE_COUNTS[f"mbpp_{task}"]
    assert all(r.passed for r in results), [r.summary() for r in results]


@pytest.mark.parametrize("task", [758, 779])
def test_mbpp_immutable_sequences_work_as_map_keys(task):
    helpers = (MBPP_DIR / f"mbpp_{task}.ae").read_text().split("@doc(")[0]
    source = (
        helpers
        + """
def main (_:Int) : Bool :=
    let counts := Map.set (Map.new : (Map (List Value1) Int))
        [Value1.asInt 1, Value1.asString "a"] 2 in
    let counts := Map.set counts [Value1.asInt 1, Value1.asString "a"] 3 in
    Map.get_or counts [Value1.asInt 1, Value1.asString "a"] 0 = 3 &&
    Map.get_or counts [Value1.asString "a", Value1.asInt 1] 0 = 0 &&
    Map.get_or counts [Value1.asInt 1] 0 = 0;
"""
    )
    driver = AeonDriver(AeonConfig("random_search", SilentSynthesisUI(), 0, no_main=False))
    assert not driver.parse(aeon_code=source)
    assert driver.run() is True


@pytest.mark.parametrize(
    "task, assertion, expected",
    [
        (7, "same_elements [1, 1, 2] [2, 1]", True),
        (7, "same_elements [1] [1, 2]", False),
        (82, "close 1.0005 1.0 0.001 0.0", True),
        (82, "close 1.1 1.0 0.001 0.0", False),
        (82, "close 0.0005 0.0 0.0 0.001", True),
        (82, "close (native \"float('inf')\" : Float) 1.0 0.001 0.0", False),
        (82, "close (native \"float('nan')\" : Float) 1.0 0.001 0.0", False),
    ],
)
def test_special_example_comparisons_preserve_original_semantics(task, assertion, expected):
    helpers = (MBPP_DIR / f"mbpp_{task}.ae").read_text().split("@doc(")[0]
    driver = AeonDriver(AeonConfig("random_search", SilentSynthesisUI(), 0, no_main=False))
    assert not driver.parse(aeon_code=f"{helpers}\ndef main (_:Int) : Bool := {assertion};")
    assert driver.run() is expected
