"""Benchmark DataFrame column pipelines: pandas vs Aeon+Array vs Aeon+LLVM.

uv run python scripts/bench_dataframe_pipeline.py
"""

from __future__ import annotations

import argparse
import json
import statistics
import tempfile
import time
from pathlib import Path

import numpy as np
import pandas as pd

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


def _time_ms(fn, repeat: int) -> float:
    samples = []
    for _ in range(repeat):
        start = time.perf_counter_ns()
        fn()
        samples.append((time.perf_counter_ns() - start) / 1e6)
    return statistics.median(samples)


def _write_csv(path: Path, n: int) -> None:
    df = pd.DataFrame({"score": np.linspace(0.0, 1.0, n), "dept": np.where(np.arange(n) % 2 == 0, "a", "b")})
    df.to_csv(path, index=False)


def _pandas_scale(path: Path) -> float:
    df = pd.read_csv(path)
    df["score"] = df["score"] * 2.0
    return float(df["score"].mean())


def _aeon_scale(path: Path, n: int, use_llvm: bool) -> float:
    kernel = (
        """
@llvm
def times_two (x: Float) : Float := x * 2.0;
@llvm
def scale_col (1 col: (Array Float)) (n: Int) : {r: (Array Float) | size r = n} :=
    map_n_float times_two col n;
"""
        if use_llvm
        else """
def times_two (x: Float) : Float := x * 2.0;
def scale_col (1 col: (Array Float)) (n: Int) : {r: (Array Float) | size r = n} :=
    map_n_float times_two col n;
"""
    )
    source = f"""
open DataFrame
open Array
{kernel}
def main (i:Int) : Float :=
    let 1 df0 := read_csv "{path}" {n} 2 in
    let pr := copy df0 in
    let 1 left := fst_df pr in
    let 1 right := snd_df pr in
    let 1 col := col_as_array left "score" in
    let 1 scaled := scale_col col {n} in
    let 1 df2 := set_col right "score" scaled in
    let 1 out := col_as_array df2 "score" in
    mean out;
"""
    cfg = AeonConfig(synthesizer="none", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    driver = AeonDriver(cfg)
    assert not driver.parse(aeon_code=source)
    return float(driver.run())


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sizes", type=int, nargs="+", default=[5_000, 20_000])
    parser.add_argument("--repeat", type=int, default=2)
    args = parser.parse_args()

    rows = []
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        for n in args.sizes:
            csv_path = tmp_path / f"data_{n}.csv"
            _write_csv(csv_path, n)
            expected = _pandas_scale(csv_path)
            pandas_ms = _time_ms(lambda: _pandas_scale(csv_path), args.repeat)
            interp_ms = _time_ms(lambda: _aeon_scale(csv_path, n, False), args.repeat)
            llvm_ms = _time_ms(lambda: _aeon_scale(csv_path, n, True), args.repeat)
            got_interp = _aeon_scale(csv_path, n, False)
            got_llvm = _aeon_scale(csv_path, n, True)
            assert abs(got_interp - expected) < 1e-5
            assert abs(got_llvm - expected) < 1e-5
            rows.append(
                {
                    "n": n,
                    "pandas_ms": round(pandas_ms, 3),
                    "aeon_interp_ms": round(interp_ms, 3),
                    "aeon_llvm_ms": round(llvm_ms, 3),
                }
            )
            print(rows[-1])
    print(json.dumps(rows, indent=2))


if __name__ == "__main__":
    main()
