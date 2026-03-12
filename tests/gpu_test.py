from aeon.backend.evaluator import eval
from aeon.facade.driver import AeonDriver, AeonConfig
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.terminal import TerminalUI

setup_logger()


def get_metadata_for_name(metadata, name_str):
    for name, meta in metadata.items():
        if name.name == name_str:
            return meta
    return {}


def test_gpu_map_execution():
    code = r"""
    import "Gpu.ae";

    def square (x:Int) : Int {
        x * x
    }

    @gpu
    def square_kernel (a:Tensor) : Tensor {
        gpu_map square a
    }

    def main (args:Int) : Tensor {
        let t : Tensor = native "[1,2,3,4,5]";
        let config = GpuConfig_of 256 1;
        run_gpu square_kernel config t
    }
    """
    cfg = AeonConfig(
        synthesizer="gp",
        synthesis_ui=TerminalUI(),
        synthesis_budget=60,
        no_main=False,
    )
    driver = AeonDriver(cfg)
    errors = driver.parse(aeon_code=code)
    assert not errors, f"error parsing : {errors}"

    kernel_metadata = get_metadata_for_name(driver.metadata, "square_kernel")
    assert kernel_metadata.get("gpu")

    print()
    result = eval(driver.core, driver.evaluation_ctx)
    print(result)
    assert result == [1, 4, 9, 16, 25], f"expected [1, 4, 9, 16, 25], got {result}"


def test_gpu_imap_execution():
    code = r"""
    import "Gpu.ae";

    def double_at_index (i:Int) : Int {
        i * 2
    }

    @gpu
    def imap_kernel (a:Tensor) : Tensor {
        gpu_imap double_at_index a
    }

    def main (args:Int) : Tensor {
        let t : Tensor = native "[10,20,30]";
        let config = GpuConfig_of 256 1;
        run_gpu imap_kernel config t
    }
    """
    cfg = AeonConfig(
        synthesizer="gp",
        synthesis_ui=TerminalUI(),
        synthesis_budget=60,
        no_main=False,
    )
    driver = AeonDriver(cfg)
    errors = driver.parse(aeon_code=code)
    assert not errors, f"error parsing : {errors}"

    kernel_metadata = get_metadata_for_name(driver.metadata, "imap_kernel")
    assert kernel_metadata.get("gpu")

    result = eval(driver.core, driver.evaluation_ctx)
    assert result == [0, 2, 4], f"expected [0, 2, 4], got {result}"


def test_gpu_reduce_execution():
    code = r"""
    import "Gpu.ae";

    def add (x:Int) (y:Int) : Int {
        x + y
    }

    @gpu
    def sum_kernel (a:Tensor) : Int {
        gpu_reduce add 0 a
    }

    def main (args:Int) : Int {
        let t : Tensor = native "[1, 2, 3, 4, 5]";
        let config = GpuConfig_of 256 1;
        run_gpu sum_kernel config t
    }
    """
    cfg = AeonConfig(
        synthesizer="gp",
        synthesis_ui=TerminalUI(),
        synthesis_budget=60,
        no_main=False,
    )
    driver = AeonDriver(cfg)
    errors = driver.parse(aeon_code=code)
    assert not errors, f"error parsing : {errors}"

    result = eval(driver.core, driver.evaluation_ctx)
    assert result == 15, f"expected 15, got {result}"


def test_gpu_filter_execution():
    code = r"""
    import "Gpu.ae";

    def is_even (x:Int) : Bool {
        (x % 2) == 0
    }

    @gpu
    def filter_kernel (a:Tensor) : Tensor {
        gpu_filter is_even a
    }

    def main (args:Int) : Tensor {
        let t : Tensor = native "[1,2,3,4,5,6]";
        let config = GpuConfig_of 256 1;
        run_gpu filter_kernel config t
    }
    """
    cfg = AeonConfig(
        synthesizer="gp",
        synthesis_ui=TerminalUI(),
        synthesis_budget=60,
        no_main=False,
    )
    driver = AeonDriver(cfg)
    errors = driver.parse(aeon_code=code)
    assert not errors, f"error parsing : {errors}"

    result = eval(driver.core, driver.evaluation_ctx)
    assert result == [2, 4, 6], f"expected [2, 4, 6], got {result}"


# def test_gpu_dot_execution():
#     code = r"""
#     import "Gpu.ae";
#
#     @gpu
#     def dot_kernel (a:Tensor) (b:Tensor) : Float {
#         gpu_dot a b
#     }
#
#     def main (args:Int) : Float {
#         let t1 : Tensor = native "[1,2,3]";
#         let t2 : Tensor = native "[4,5,6]";
#         let config = GpuConfig_of 256 1;
#         run_gpu (\t:Tensor -> dot_kernel t2 t) config t1
#     }
#
#     """
#     cfg = AeonConfig(
#         synthesizer="gp",
#         synthesis_ui=TerminalUI(),
#         synthesis_budget=60,
#         no_main=False,
#     )
#     driver = AeonDriver(cfg)
#     errors = driver.parse(aeon_code=code)
#     assert not errors, f"error parsing : {errors}"
#
#     result = eval(driver.core, driver.evaluation_ctx)
#     assert result == 32.0, f"expected 32.0, got {result}"
