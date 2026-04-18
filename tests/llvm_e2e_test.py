import sys

import pytest
from loguru import logger
from aeon.facade.driver import AeonDriver, AeonConfig
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SilentSynthesisUI


def compile_and_run(source: str):
    setup_logger()
    logger.add(sys.stderr, level="DEBUG")

    cfg = AeonConfig(synthesizer="random_search", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    driver = AeonDriver(cfg)
    errors = driver.parse(aeon_code=source)
    assert not errors
    return driver.run()


def test_e2e_sum_floats():
    source = r"""
    @llvm
    def special_sum (x:Float) (y:Float) : Float {
        let w : Float = 5.0;
        let z : Float = 10.0;
        x + y - z * w
    }

    def main (i:Int) : Float { special_sum 5.0 7.0 }
    """
    res = compile_and_run(source)
    assert res == -38.0


def test_e2e_recursive():
    source = r"""
    @llvm
    def count_divisors (target:Int) (candidate:Int) : Int {
        if candidate <= 0 then
            0
        else
            let remainder : Int = target % candidate;
            if remainder == 0 then
                1 + count_divisors target (candidate - 1)
            else
                count_divisors target (candidate - 1)
    }

    def main (i:Int) : Int { count_divisors 100 50 }
    """
    res = compile_and_run(source)
    assert res == 8


def test_e2e_llvm_fibonacci():
    source = r"""
    @llvm
    def fib(n:Int) : Int {
        if n <= 1 then n else fib (n-1) + fib (n-2)
    }

    def main (i:Int) : Int { fib 10 }
    """
    res = compile_and_run(source)
    assert res == 55


@pytest.mark.skip(reason="Parametric Vector.ae + elaboration (unification/hash) not yet aligned with master")
def test_e2e_llvm_matrix_sum():
    source = r"""
    import "Vector.ae";

    @llvm
    def add(acc:Int) (curr:Int) : Int { acc + curr }

    @llvm
    def sum_matrix(m:(Vector Int)) (s:Int) : Int {
        Vector_reduce[Int][Int] add 0 m s
    }

    def main (i:Int) : Int { sum_matrix (native "[1, 2, 3, 4]") 4 }
    """
    res = compile_and_run(source)
    assert res == 10


@pytest.mark.skip(reason="Parametric Vector.ae + elaboration (unification/hash) not yet aligned with master")
def test_e2e_llvm_matrix_filter():
    source = r"""
    import "Vector.ae";

    @llvm
    def filter_even(m:(Vector Int)) (s:Int) : (Vector Int) {
        Vector_filter[Int] (\x:Int -> x % 2 == 0) m s
    }


    def main (i:Int) : Int {
        let m : (Vector Int) = native "[1, 2, 3, 4, 5, 6]" in
        let filtered : (Vector Int) = filter_even m 6 in
        Vector_get[Int] filtered 0
    }
    """
    res = compile_and_run(source)
    assert res == 2


@pytest.mark.skip(reason="Parametric Vector.ae + elaboration (unification/hash) not yet aligned with master")
def test_e2e_llvm_matrix_zip_with():
    source = r"""
    import "Vector.ae";

    @llvm
    def vec_add(v1:(Vector Int)) (v2:(Vector Int)) (s:Int) : (Vector Int) {
        Vector_zipWith[Int][Int][Int] (\x:Int -> \y:Int -> x + y) v1 v2 s
    }


    def main (i:Int) : Int {
        let v1 : (Vector Int) = native "[1, 2, 3]" in
        let v2 : (Vector Int) = native "[10, 20, 30]" in
        let v3 : (Vector Int) = vec_add v1 v2 3 in
        Vector_get[Int] v3 1
    }
    """
    res = compile_and_run(source)
    assert res == 22


@pytest.mark.skip(reason="Parametric Vector.ae + elaboration (unification/hash) not yet aligned with master")
def test_e2e_llvm_matrix_count():
    source = r"""
    import "Vector.ae";

    @llvm
    def count_gt_10(v:(Vector Int)) (s:Int) : Int {
        Vector_count[Int] (\x:Int -> x > 10) v s
    }

    def main (i:Int) : Int {
        let v : (Vector Int) = native "[5, 15, 8, 25, 3]" in
        count_gt_10 v 5
    }
    """
    res = compile_and_run(source)
    assert res == 2


@pytest.mark.skip(reason="Parametric Vector.ae + elaboration (unification/hash) not yet aligned with master")
def test_e2e_llvm_matrix_map():
    source = r"""
    import "Vector.ae";

    @llvm
    def vec_inc(v:(Vector Int)) (s:Int) : (Vector Int) {
        Vector_map[Int][Int] (\x:Int -> x + 1) v s
    }


    def main (i:Int) : Int {
        let v : (Vector Int) = native "[1, 2, 3, 4, 5]" in
        let v2 : (Vector Int) = vec_inc v 5 in
        Vector_get[Int] v2 2
    }
    """
    res = compile_and_run(source)
    assert res == 4


def test_e2e_llvm_math_integration():
    source = r"""
    import "Math.ae";

    @llvm
    def compute_circle_area(radius:Float) : Float {
        Math_PI * Math_powf radius 2.0
    }

    def main (i:Int) : Float { compute_circle_area 5.0 }
    """
    res = compile_and_run(source)
    assert abs(res - 78.53981633974483) < 1e-5
