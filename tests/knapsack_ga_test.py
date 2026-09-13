"""Knapsack GA single-kernel correctness (CPU IR path; GPU when available)."""

from __future__ import annotations

import pytest

from aeon.bindings.knapsack_ga import make_random_instance, run_cpu, run_random_cpu, run_random_gpu
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.llvm.kernels.knapsack_ga_ir import knapsack_ga_ir
from aeon.synthesis.uis.api import SilentSynthesisUI


def _cuda_available() -> bool:
    try:
        from aeon.llvm.cuda.executor import CUDAExecutionEngine

        CUDAExecutionEngine()
        return True
    except Exception:
        return False


def test_knapsack_ir_parses():
    ir = knapsack_ga_ir(nvptx=False)
    assert "knapsack_ga" in ir
    assert "knapsack_ga__kernel" in ir
    nv = knapsack_ga_ir(nvptx=True)
    assert "nvptx64-nvidia-cuda" in nv
    assert "nvvm.annotations" in nv


def test_knapsack_cpu_nonnegative():
    weights, values, capacity = make_random_instance(40, seed=7)
    best = run_cpu(weights, values, 40, capacity, pop_size=32, generations=50, seed=7)
    assert best >= 0


def test_knapsack_cpu_deterministic():
    assert run_random_cpu(30, 20, 25, seed=11) == run_random_cpu(30, 20, 25, seed=11)


def test_knapsack_aeon_cpu_wrapper():
    source = """
open KnapsackGA
def main (i:Int) : Int := run_random_cpu 20 16 30 3;
"""
    cfg = AeonConfig(synthesizer="none", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    driver = AeonDriver(cfg)
    assert not driver.parse(aeon_code=source)
    assert driver.run() >= 0


@pytest.mark.skipif(not _cuda_available(), reason="CUDA unavailable")
def test_knapsack_gpu_smoke():
    assert run_random_gpu(64, 16, 40, 5) >= 0
