import pytest
from aeon.facade.driver import AeonDriver, AeonConfig
from aeon.synthesis.uis.api import SynthesisUI
from aeon.logger.logger import setup_logger

setup_logger()


@pytest.mark.skip(
    reason="Elaboration does not yet support polymorphic Vector in this program (was skip_elaboration on PR #141)."
)
def test_gpu_fallback():
    aeon_code = """
        import "Vector.ae";

        @gpu(target="cuda", debug=false, cache=false, block_size=32, thread_count=1024)
        def multiply_by_two (v:(Vector Int)) (size:Int) : (Vector Int) =
            Vector_map[Int][Int] (\\x:Int -> x * 2) v size;

        def main (args:Int) : Int =
            let v : (Vector Int) = Vector_new[Int] in
            let v2 : (Vector Int) = Vector_append[Int] v 10 in
            let v3 : (Vector Int) = Vector_append[Int] v2 20 in
            let res : (Vector Int) = multiply_by_two v3 2 in
            Vector_get[Int] res 0;
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
        def gpu_add (a:Int) (b:Int) : Int = a + b;

        def main (args:Int) : Int = gpu_add 5 7;
    """
    config = AeonConfig(synthesizer="none", synthesis_ui=SynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(config)
    errors = driver.parse(aeon_code=aeon_code)
    assert not errors
    result = driver.run()
    assert result == 12
