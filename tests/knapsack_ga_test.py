"""Knapsack GA examples (not stdlib): typecheck + CPU demo smoke."""

from __future__ import annotations

from pathlib import Path

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI

ROOT = Path(__file__).resolve().parents[1]
CPU_EXAMPLE = ROOT / "examples" / "llvm" / "knapsack_ga_cpu.ae"
GPU_EXAMPLE = ROOT / "examples" / "llvm" / "gpu" / "knapsack_ga.ae"


def _driver() -> AeonDriver:
    return AeonDriver(
        AeonConfig(synthesizer="none", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=False)
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


def test_knapsack_cpu_example_typechecks():
    driver = _driver()
    assert not driver.parse(filename=str(CPU_EXAMPLE))


def test_knapsack_gpu_example_typechecks():
    driver = _driver()
    assert not driver.parse(filename=str(GPU_EXAMPLE))
