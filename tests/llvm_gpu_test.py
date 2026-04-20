import pytest
from aeon.facade.driver import AeonDriver, AeonConfig
from aeon.synthesis.uis.api import SynthesisUI
from aeon.logger.logger import setup_logger

setup_logger()


@pytest.mark.skip(reason="Parametric Vector.ae + elaboration (unification/hash) not yet aligned with master")
def test_gpu_fallback():
    aeon_code = """
        @gpu(target="cuda", debug=false, cache=false, block_size=32, thread_count=1024)
        def multiply_by_two (v : Vector Int) (size:Int) : (Vector Int) {
            Vector_map[Int][Int] (\\x:Int -> x * 2) v size
        }

        def main (args:Int) : Int {
            let v : (Vector Int) = Vector_new[Int];
            let v2 : (Vector Int) = Vector_append[Int] v 10;
            let v3 : (Vector Int) = Vector_append[Int] v2 20;
            let res : (Vector Int) = multiply_by_two v3 2;
            Vector_get[Int] res 0
        }
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
        def gpu_add (a:Int) (b:Int) : Int {
            a + b
        }

        def main (args:Int) : Int {
            gpu_add 5 7
        }
    """
    config = AeonConfig(synthesizer="none", synthesis_ui=SynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(config)
    errors = driver.parse(aeon_code=aeon_code)
    assert not errors
    result = driver.run()
    assert result == 12
