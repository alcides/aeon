"""Functional knapsack GA example: typecheck + smoke run."""

from __future__ import annotations

from pathlib import Path

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI

ROOT = Path(__file__).resolve().parents[1]
EXAMPLE = ROOT / "examples" / "knapsack_ga.ae"


def _driver(*, no_main: bool = False) -> AeonDriver:
    return AeonDriver(
        AeonConfig(synthesizer="none", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=no_main)
    )


def test_fold_n_int_llvm():
    cfg = AeonConfig(synthesizer="none", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    driver = AeonDriver(cfg)
    source = """
open LoopKernels
@llvm
def add_i (acc: Int) (i: Int) : Int := acc + i;
@llvm
def sum_range (n: Int) : Int := fold_n_int add_i 0 n;
def main (x: Int) : Int := sum_range 10;
"""
    assert not driver.parse(aeon_code=source)
    assert driver.run() == 45


def test_knapsack_ga_example_typechecks():
    driver = _driver()
    assert not driver.parse(filename=str(EXAMPLE))


def test_knapsack_ga_example_runs():
    driver = _driver()
    assert not driver.parse(filename=str(EXAMPLE))
    result = driver.run()
    assert isinstance(result, int)
    assert result >= 0
