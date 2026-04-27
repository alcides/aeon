from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SynthesisUI

from tests.driver import check_and_return_core

setup_logger()


def _metadata_from_driver(source: str):
    cfg = AeonConfig(synthesizer="none", synthesis_ui=SynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(cfg)
    errors = driver.parse(aeon_code=source)
    assert not errors
    return driver.metadata


def test_gpu_decorator_defaults():
    source = """
    @gpu
    def max(a:Int) (b:Int) : Int = if a > b then a else b;
    def main (x:Int) : Int = max 1 2;
    """
    metadata = _metadata_from_driver(source)
    gpu_funcs = [k for k, v in metadata.items() if isinstance(v, dict) and v.get("gpu")]
    assert len(gpu_funcs) == 1

    max_meta = metadata[gpu_funcs[0]]
    assert max_meta["gpu_device"] == "cuda"
    assert max_meta["gpu_target"] == ""
    assert max_meta["gpu_opt_level"] == 3
    assert max_meta["gpu_log_ir"] is False
    assert max_meta["gpu_debug"] is False
    assert max_meta["gpu_cache"] is False
    assert max_meta["gpu_block_size"] == 32
    assert max_meta["gpu_thread_count"] == 128


def test_gpu_decorator_with_args():
    source = r"""
    @gpu("cuda", "sm_60", 2, true, true, true, 256, 128)
    def max(a:Int) (b:Int) : Int = if a > b then a else b;
    def main (x:Int) : Int = max 1 2;
    """
    metadata = _metadata_from_driver(source)
    gpu_funcs = [k for k, v in metadata.items() if isinstance(v, dict) and v.get("gpu")]
    assert len(gpu_funcs) == 1

    max_meta = metadata[gpu_funcs[0]]
    assert max_meta["gpu_device"] == "cuda"
    assert max_meta["gpu_target"] == "sm_60"
    assert max_meta["gpu_opt_level"] == 2
    assert max_meta["gpu_log_ir"] is True
    assert max_meta["gpu_debug"] is True
    assert max_meta["gpu_cache"] is True
    assert max_meta["gpu_block_size"] == 256
    assert max_meta["gpu_thread_count"] == 128


def test_llvm_decorator_defaults():
    source = """
    @llvm
    def max(a:Int) (b:Int) : Int = if a > b then a else b;
    def main (x:Int) : Int = max 1 2;
    """
    metadata = _metadata_from_driver(source)
    llvm_funcs = [k for k, v in metadata.items() if isinstance(v, dict) and v.get("llvm")]
    assert len(llvm_funcs) == 1

    max_meta = metadata[llvm_funcs[0]]
    assert max_meta["llvm_opt_level"] == 3
    assert max_meta["llvm_log_ir"] is False
    assert max_meta["llvm_debug"] is False
    assert max_meta["llvm_cache"] is False


def test_gpu_decorator_with_named_args():
    source = r"""
    @gpu(device="cuda", target="sm_60", opt_level=2, log_ir=true, debug=true, cache=true, block_size=256, thread_count=128)
    def max(a:Int) (b:Int) : Int = if a > b then a else b;
    def main (x:Int) : Int = max 1 2;
    """
    metadata = _metadata_from_driver(source)
    gpu_funcs = [k for k, v in metadata.items() if isinstance(v, dict) and v.get("gpu")]
    assert len(gpu_funcs) == 1

    max_meta = metadata[gpu_funcs[0]]
    assert max_meta["gpu_device"] == "cuda"
    assert max_meta["gpu_target"] == "sm_60"
    assert max_meta["gpu_opt_level"] == 2
    assert max_meta["gpu_log_ir"] is True
    assert max_meta["gpu_debug"] is True
    assert max_meta["gpu_cache"] is True
    assert max_meta["gpu_block_size"] == 256
    assert max_meta["gpu_thread_count"] == 128


def test_llvm_decorator_with_named_args():
    source = r"""
    @llvm(opt_level=1, log_ir=true, cache=true, debug=true)
    def max(a:Int) (b:Int) : Int = if a > b then a else b;
    def main (x:Int) : Int = max 1 2;
    """
    metadata = _metadata_from_driver(source)
    llvm_funcs = [k for k, v in metadata.items() if isinstance(v, dict) and v.get("llvm")]
    assert len(llvm_funcs) == 1

    max_meta = metadata[llvm_funcs[0]]
    assert max_meta["llvm_opt_level"] == 1
    assert max_meta["llvm_log_ir"] is True
    assert max_meta["llvm_debug"] is True
    assert max_meta["llvm_cache"] is True


def test_core_queue_cleared_after_typecheck():
    """Queued ``@llvm`` metadata is applied in core phase (not left on sugar-only desugar)."""
    source = """
    @llvm
    def f(x:Int) : Int = x + 1;
    def main (x:Int) : Int = f x;
    """
    _, _, _, metadata = check_and_return_core(source)
    from aeon.decorators.api import CORE_DECORATOR_QUEUE_META_KEY

    assert CORE_DECORATOR_QUEUE_META_KEY not in metadata
    llvm_keys = [k for k, v in metadata.items() if isinstance(v, dict) and v.get("llvm")]
    assert len(llvm_keys) >= 1
