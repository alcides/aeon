import sys

import pytest
from loguru import logger
from aeon.facade.driver import AeonDriver, AeonConfig
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SilentSynthesisUI


def compile_and_run(source: str):
    setup_logger()
    logger.add(sys.stderr, level="DEBUG")

    cfg = AeonConfig(
        synthesizer="random_search",
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=0,
        no_main=True,
    )
    driver = AeonDriver(cfg)
    errors = driver.parse(aeon_code=source)
    assert not errors
    return driver.run()


def test_e2e_sum_floats():
    source = r"""
    @llvm
    def special_sum (x:Float) (y:Float) : Float :=
        let w : Float := 5.0 in
        let z : Float := 10.0 in
        x + y - z * w;

    def main (i:Int) : Float := special_sum 5.0 7.0;
    """
    res = compile_and_run(source)
    assert res == -38.0


def test_e2e_recursive():
    source = r"""
    @llvm
    def count_divisors (target:Int) (candidate:Int) : Int :=
        if candidate <= 0 then 0 else
        let remainder : Int := target % candidate in
        if remainder = 0 then 1 + count_divisors target (candidate - 1)
        else count_divisors target (candidate - 1);

    def main (i:Int) : Int := count_divisors 100 50;
    """
    res = compile_and_run(source)
    assert res == 8


def test_e2e_llvm_fibonacci():
    source = r"""
    @llvm
    def fib(n:Int) : Int := if n <= 1 then n else fib (n-1) + fib (n-2);

    def main (i:Int) : Int := fib 10;
    """
    res = compile_and_run(source)
    assert res == 55


def test_e2e_llvm_array_sum():
    source = r"""
    open Array

    @llvm
    def add(acc:Int) (curr:Int) : Int := acc + curr;

    @llvm
    def sum_matrix(1 m:(Array Int)) (s:Int) : Int := reduce_n_int add 0 m s;

    def main (i:Int) : Int :=
        let 1 a0 := new{Int} unit in
        let 1 a1 := append{Int} a0 1 in
        let 1 a2 := append{Int} a1 2 in
        let 1 a3 := append{Int} a2 3 in
        let 1 a4 := append{Int} a3 4 in
        sum_matrix a4 4;
    """
    res = compile_and_run(source)
    assert res == 10


def test_e2e_llvm_array_map():
    source = r"""
    open Array

    @llvm
    def inc(x:Int) : Int := x + 1;

    @llvm
    def vec_inc(1 v:(Array Int)) (s:Int) : {r:(Array Int) | size r = s} :=
        map_n_int inc v s;

    def main (i:Int) : Int :=
        let 1 a0 := new{Int} unit in
        let 1 a1 := append{Int} a0 1 in
        let 1 a2 := append{Int} a1 2 in
        let 1 a3 := append{Int} a2 3 in
        let 1 a4 := append{Int} a3 4 in
        let 1 a5 := append{Int} a4 5 in
        let 1 v2 := vec_inc a5 5 in
        get{Int} v2 2;
    """
    res = compile_and_run(source)
    assert res == 4


def test_e2e_llvm_array_count():
    source = r"""
    open Array

    @llvm
    def gt10(x:Int) : Bool := x > 10;

    @llvm
    def count_gt_10(1 v:(Array Int)) (s:Int) : Int :=
        count_n_int gt10 v s;

    def main (i:Int) : Int :=
        let 1 a0 := new{Int} unit in
        let 1 a1 := append{Int} a0 5 in
        let 1 a2 := append{Int} a1 15 in
        let 1 a3 := append{Int} a2 8 in
        let 1 a4 := append{Int} a3 25 in
        let 1 a5 := append{Int} a4 3 in
        count_gt_10 a5 5;
    """
    res = compile_and_run(source)
    assert res == 2


@pytest.mark.skip(
    reason="filter_n_int return length is data-dependent; size refinements not yet tracked for LLVM filter."
)
def test_e2e_llvm_array_filter():
    source = r"""
    open Array

    @llvm
    def even(x:Int) : Bool := x % 2 = 0;

    @llvm
    def filter_even(1 m:(Array Int)) (s:Int) : (Array Int) :=
        filter_n_int even m s;

    def main (i:Int) : Int :=
        let 1 a0 := new{Int} unit in
        let 1 a1 := append{Int} a0 1 in
        let 1 a2 := append{Int} a1 2 in
        let 1 a3 := append{Int} a2 3 in
        let 1 a4 := append{Int} a3 4 in
        let 1 filtered := filter_even a4 4 in
        get{Int} filtered 0;
    """
    res = compile_and_run(source)
    assert res == 2


def test_e2e_llvm_array_zip_with():
    source = r"""
    open Array

    @llvm
    def add2(x:Int) (y:Int) : Int := x + y;

    @llvm
    def vec_add(1 v1:(Array Int)) (1 v2:(Array Int)) (s:Int) : {r:(Array Int) | size r = s} :=
        zipWith_n_int add2 v1 v2 s;

    def main (i:Int) : Int :=
        let 1 a0 := new{Int} unit in
        let 1 a1 := append{Int} a0 1 in
        let 1 a2 := append{Int} a1 2 in
        let 1 a3 := append{Int} a2 3 in
        let 1 b0 := new{Int} unit in
        let 1 b1 := append{Int} b0 10 in
        let 1 b2 := append{Int} b1 20 in
        let 1 b3 := append{Int} b2 30 in
        let 1 v3 := vec_add a3 b3 3 in
        get{Int} v3 1;
    """
    res = compile_and_run(source)
    assert res == 22


def test_e2e_llvm_math_integration():
    source = r"""
    open Math

    @llvm
    def compute_circle_area(radius:Float) : Float := Math.PI * Math.powf radius 2.0;

    def main (i:Int) : Float := compute_circle_area 5.0;
    """
    res = compile_and_run(source)
    assert abs(res - 78.53981633974483) < 1e-5
