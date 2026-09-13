"""Benchmark Array kernels: interpreter vs ``@llvm`` vs numpy.

  uv run python scripts/bench_array_kernels.py
  uv run python scripts/bench_array_kernels.py --sizes 100000 1000000
"""

from __future__ import annotations

import argparse
import json
import statistics
import time

import numpy as np

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


def _time_ms(fn, repeat: int) -> float:
    samples = []
    for _ in range(repeat):
        start = time.perf_counter_ns()
        fn()
        samples.append((time.perf_counter_ns() - start) / 1e6)
    return statistics.median(samples)


def _prepare(source: str) -> AeonDriver:
    cfg = AeonConfig(synthesizer="none", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    driver = AeonDriver(cfg)
    assert not driver.parse(aeon_code=source)
    return driver


def _aeon_sum_source(n: int, llvm: bool) -> str:
    if llvm:
        return f"""
open Array
@llvm
def add(acc:Int) (curr:Int) : Int := acc + curr;
@llvm
def sum_n (1 arr:(Array Int)) (n:Int) : Int := reduce_n_int add 0 arr n;
def main (i:Int) : Int :=
    let 1 xs := native "list(range({n}))" in
    sum_n xs {n};
"""
    return f"""
open Array
def main (i:Int) : Int :=
    let 1 xs := native "list(range({n}))" in
    sum xs;
"""


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sizes", type=int, nargs="+", default=[10_000, 100_000])
    parser.add_argument("--repeat", type=int, default=3)
    args = parser.parse_args()

    rows = []
    for n in args.sizes:
        data = list(range(n))
        expected = n * (n - 1) // 2
        numpy_ms = _time_ms(lambda: np.sum(np.asarray(data, dtype=np.int64)), args.repeat)
        assert int(np.sum(np.asarray(data, dtype=np.int64))) == expected

        interp_driver = _prepare(_aeon_sum_source(n, llvm=False))
        llvm_driver = _prepare(_aeon_sum_source(n, llvm=True))
        assert interp_driver.run() == expected
        assert llvm_driver.run() == expected

        # Re-prepare so each timed run is a fresh evaluation with compiled IR ready.
        interp_ms = _time_ms(lambda: _prepare(_aeon_sum_source(n, False)).run(), args.repeat)
        llvm_ms = _time_ms(lambda: _prepare(_aeon_sum_source(n, True)).run(), args.repeat)
        rows.append(
            {
                "n": n,
                "numpy_ms": round(numpy_ms, 3),
                "aeon_interp_ms": round(interp_ms, 3),
                "aeon_llvm_ms": round(llvm_ms, 3),
                "note": "aeon_* times include parse+compile+eval end-to-end",
            }
        )
        print(rows[-1])

    print(json.dumps(rows, indent=2))


if __name__ == "__main__":
    main()
