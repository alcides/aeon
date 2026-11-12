"""Array + LLVM/GPU kernels and DataFrame column bridge."""

from __future__ import annotations

import csv
from pathlib import Path

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SilentSynthesisUI


def _run(source: str):
    setup_logger()
    cfg = AeonConfig(
        synthesizer="none",
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=0,
        no_main=True,
    )
    driver = AeonDriver(cfg)
    errors = driver.parse(aeon_code=source)
    assert not errors, errors
    return driver.run()


def test_llvm_array_reduce_sum():
    source = r"""
open Array
open ArrayKernels

@llvm
def add(acc:Int) (curr:Int) : Int := acc + curr;

@llvm
def sum_n (1 arr:(Array Int)) (n:Int) : Int :=
    reduce_n_int add 0 arr n;

def main (i:Int) : Int :=
    let 1 a0 := Array.mk_empty{Int} unit in
    let 1 a1 := Array.mk_concat a0 (Array.mk_1 1) in
    let 1 a2 := Array.mk_concat a1 (Array.mk_1 2) in
    let 1 a3 := Array.mk_concat a2 (Array.mk_1 3) in
    let 1 a4 := Array.mk_concat a3 (Array.mk_1 4) in
    sum_n a4 4;
"""
    assert _run(source) == 10


def test_llvm_array_map_inc():
    source = r"""
open Array
open ArrayKernels

@llvm
def inc(x:Int) : Int := x + 1;

@llvm
def vec_inc (1 arr:(Array Int)) (n:Int) : {r:(Array Int) | size r = n} :=
    map_n_int inc arr n;

def main (i:Int) : Int :=
    let 1 a0 := Array.mk_empty{Int} unit in
    let 1 a1 := Array.mk_concat a0 (Array.mk_1 1) in
    let 1 a2 := Array.mk_concat a1 (Array.mk_1 2) in
    let 1 a3 := Array.mk_concat a2 (Array.mk_1 3) in
    let 1 r := vec_inc a3 3 in
    Array.take{Int} r 2;
"""
    assert _run(source) == 4


def test_llvm_array_count():
    source = r"""
open Array
open ArrayKernels

@llvm
def gt10(x:Int) : Bool := x > 10;

@llvm
def c (1 arr:(Array Int)) (n:Int) : Int := count_n_int gt10 arr n;

def main (i:Int) : Int :=
    let 1 a0 := Array.mk_empty{Int} unit in
    let 1 a1 := Array.mk_concat a0 (Array.mk_1 5) in
    let 1 a2 := Array.mk_concat a1 (Array.mk_1 15) in
    let 1 a3 := Array.mk_concat a2 (Array.mk_1 8) in
    let 1 a4 := Array.mk_concat a3 (Array.mk_1 25) in
    let 1 a5 := Array.mk_concat a4 (Array.mk_1 3) in
    c a5 5;
"""
    assert _run(source) == 2


def test_gpu_array_map_fallback():
    """``@gpu`` falls back to CPU when CUDA is unavailable."""
    source = r"""
open Array
open ArrayKernels

@gpu
def inc(x:Int) : Int := x + 1;

@gpu
def vec_inc (1 arr:(Array Int)) (n:Int) : {r:(Array Int) | size r = n} :=
    map_n_int inc arr n;

def main (i:Int) : Int :=
    let 1 a0 := Array.mk_empty{Int} unit in
    let 1 a1 := Array.mk_concat a0 (Array.mk_1 10) in
    let 1 a2 := Array.mk_concat a1 (Array.mk_1 20) in
    let 1 r := vec_inc a2 2 in
    Array.take{Int} r 0;
"""
    assert _run(source) == 11


def test_dataframe_etl_and_column_bridge(tmp_path: Path):
    csv_path = tmp_path / "people.csv"
    with csv_path.open("w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["name", "age", "score"])
        writer.writerow(["a", "20", "1.0"])
        writer.writerow(["b", "30", "2.0"])
        writer.writerow(["c", "40", "3.0"])

    source = rf"""
open DataFrame
open Array
open ArrayKernels

def main (i:Int) : Float :=
    let 1 df0 := read_csv "{csv_path}" 3 3 in
    let 1 df1 := dropna df0 in
    let 1 pr := DataFrame.copy df1 in
    DataFrame.with_pair pr (fun left => fun right =>
    let 1 col := col_as_array left "score" in
    let _ := DataFrame.dispose left in
    let 1 scaled := scale 2.0 col in
    let 1 df3 := set_col right "score" scaled in
    let 1 col2 := col_as_array df3 "score" in
    let _ := DataFrame.dispose df3 in
    (Array.consume Array.mean) col2);
"""
    assert abs(_run(source) - 4.0) < 1e-9
