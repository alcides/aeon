from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program


def test_gpu_decorator_defaults():
    source = """
    @gpu
    def max(a:Int) (b:Int) : Int { if a > b then a else b }
    """
    prog = parse_program(source)
    desugared = desugar(prog)

    gpu_funcs = [k for k, v in desugared.metadata.items() if v.get("gpu")]
    assert len(gpu_funcs) == 1

    max_meta = desugared.metadata[gpu_funcs[0]]
    assert max_meta["gpu_device"] == "cuda"
    assert max_meta["gpu_debug"] is False
    assert max_meta["gpu_cache"] is False
    assert max_meta["gpu_block_size"] == 1
    assert max_meta["gpu_thread_count"] == 1


def test_gpu_decorator_with_args():
    source = """
    @gpu("cuda", true, true, 256, 128)
    def max(a:Int) (b:Int) : Int { if a > b then a else b }
    """
    prog = parse_program(source)
    desugared = desugar(prog)

    gpu_funcs = [k for k, v in desugared.metadata.items() if v.get("gpu")]
    assert len(gpu_funcs) == 1

    max_meta = desugared.metadata[gpu_funcs[0]]
    assert max_meta["gpu_device"] == "cuda"
    assert max_meta["gpu_debug"] is True
    assert max_meta["gpu_cache"] is True
    assert max_meta["gpu_block_size"] == 256
    assert max_meta["gpu_thread_count"] == 128


def test_llvm_decorator_defaults():
    source = """
    @llvm
    def max(a:Int) (b:Int) : Int { if a > b then a else b }
    """
    prog = parse_program(source)
    desugared = desugar(prog)

    llvm_funcs = [k for k, v in desugared.metadata.items() if v.get("llvm")]
    assert len(llvm_funcs) == 1

    max_meta = desugared.metadata[llvm_funcs[0]]
    assert max_meta["llvm_debug"] is False
    assert max_meta["llvm_cache"] is False


def test_gpu_decorator_with_named_args():
    source = """
    @gpu(target="cuda", debug=true, cache=true, block_size=256, thread_count=128)
    def max(a:Int) (b:Int) : Int { if a > b then a else b }
    """
    prog = parse_program(source)
    desugared = desugar(prog)

    gpu_funcs = [k for k, v in desugared.metadata.items() if v.get("gpu")]
    assert len(gpu_funcs) == 1

    max_meta = desugared.metadata[gpu_funcs[0]]
    assert max_meta["gpu_device"] == "cuda"
    assert max_meta["gpu_debug"] is True
    assert max_meta["gpu_cache"] is True
    assert max_meta["gpu_block_size"] == 256
    assert max_meta["gpu_thread_count"] == 128


def test_llvm_decorator_with_named_args():
    source = """
    @llvm(cache=true, debug=true)
    def max(a:Int) (b:Int) : Int { if a > b then a else b }
    """
    prog = parse_program(source)
    desugared = desugar(prog)

    llvm_funcs = [k for k, v in desugared.metadata.items() if v.get("llvm")]
    assert len(llvm_funcs) == 1

    max_meta = desugared.metadata[llvm_funcs[0]]
    assert max_meta["llvm_debug"] is True
    assert max_meta["llvm_cache"] is True
