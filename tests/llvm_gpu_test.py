from aeon.facade.driver import AeonDriver, AeonConfig
from aeon.synthesis.uis.api import SynthesisUI
from aeon.logger.logger import setup_logger

setup_logger()


def test_gpu_array_map_fallback():
    aeon_code = """
        open Array
        open ArrayKernels

        @gpu(target:="cuda", debug:=false, cache:=false, block_size:=32, thread_count:=1024)
        def mul2 (x:Int) : Int := x * 2;

        @gpu(target:="cuda", debug:=false, cache:=false, block_size:=32, thread_count:=1024)
        def multiply_by_two (1 v:(Array Int)) (n:Int) : {r:(Array Int) | size r = n} :=
            map_n_int mul2 v n;

        def main (args:Int) : Int :=
            let 1 v0 := new{Int} unit in
            let 1 v2 := append{Int} v0 10 in
            let 1 v3 := append{Int} v2 20 in
            let 1 res := multiply_by_two v3 2 in
            get{Int} res 0;
    """
    config = AeonConfig(synthesizer="none", synthesis_ui=SynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(config)
    errors = driver.parse(aeon_code=aeon_code)
    assert not errors

    result = driver.run()
    assert result == 20


def test_gpu_sum():
    # will fall back to cpu if not executed in a CUDA env
    aeon_code = """
        @gpu
        def gpu_add (a:Int) (b:Int) : Int := a + b;

        def main (args:Int) : Int := gpu_add 5 7;
    """
    config = AeonConfig(synthesizer="none", synthesis_ui=SynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(config)
    errors = driver.parse(aeon_code=aeon_code)
    assert not errors
    result = driver.run()
    assert result == 12
