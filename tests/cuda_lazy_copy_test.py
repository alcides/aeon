"""Verify coherence and actual transfer counts between consecutive GPU calls."""

import ctypes
import gc
from pathlib import Path

import pytest

from aeon.bindings.ndarray import ManagedArray, from_array, full
from aeon.core.parser import parse_term
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.llvm.core import Backend
from aeon.llvm.cpu.converter import CPULLVMIRGenerator
from aeon.llvm.cpu.executor import CPULLVMExecutionEngine
from aeon.llvm.cuda.converter import CUDALLVMIRGenerator
from aeon.llvm.cuda.executor import CUDAExecutionEngine, CUDAExecutionError
from aeon.llvm.cuda.lowerer import CUDALLVMLowerer
from aeon.llvm.llvm_ast import LLVMFunctionType, LLVMInt, LLVMNDArrayType, LLVMPointerType
from aeon.llvm.pipeline import MultiBackendPipeline
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.name import Name
from tests.cuda_array_return_test import EmulatedCUDA


def emulated_engine():
    engine = CUDAExecutionEngine.__new__(CUDAExecutionEngine)
    engine.libcuda = EmulatedCUDA()
    engine.context = None
    engine._module_cache = {}
    engine._compile_to_ptx = lambda code: code
    engine._load_module = engine.libcuda.load_module
    engine._get_function = engine.libcuda.get_function
    return engine


@pytest.fixture(scope="module")
def real_cuda():
    try:
        engine = CUDAExecutionEngine()
    except CUDAExecutionError as exc:
        pytest.skip(str(exc))
    yield engine
    engine.close()


@pytest.fixture(params=["emulated", "cuda"])
def gpu(request):
    engine = emulated_engine() if request.param == "emulated" else request.getfixturevalue("real_cuda")
    yield engine
    engine.close()
    if isinstance(engine.libcuda, EmulatedCUDA):
        assert not engine.libcuda.allocations


@pytest.fixture
def transfers(gpu, monkeypatch):
    uploads, downloads = [], []
    upload, download = gpu.libcuda.cuMemcpyHtoD_v2, gpu.libcuda.cuMemcpyDtoH_v2

    def record_upload(destination, source, size):
        uploads.append((destination, size))
        return upload(destination, source, size)

    def record_download(destination, source, size):
        downloads.append((source, size))
        return download(destination, source, size)

    monkeypatch.setattr(gpu.libcuda, "cuMemcpyHtoD_v2", record_upload)
    monkeypatch.setattr(gpu.libcuda, "cuMemcpyDtoH_v2", record_download)
    return uploads, downloads


def function(body, types, result):
    node = CUDALLVMLowerer().lower(parse_term(body), expected_type=LLVMFunctionType(types, result))
    node.name = Name("lazy_test", 0)
    return node


def invoke(engine, node, arguments):
    if isinstance(engine.libcuda, EmulatedCUDA):
        engine.libcuda.param_types = [
            ctypes.c_void_p if isinstance(ty, (LLVMNDArrayType, LLVMPointerType)) else engine._get_ctypes_type(ty)
            for ty in node.arg_types
        ] + [ctypes.c_void_p]
    code = CUDALLVMIRGenerator().generate_ir([node])
    return engine.execute(code, "lazy_test", arguments, node.arg_types, node.type.return_type)


def set_element(gpu, array, index, value):
    ty = LLVMNDArrayType(LLVMInt, 1)
    node = function("fun a => fun i => fun v => NDArray_set1 a i v", [ty, LLVMInt, LLVMInt], ty)
    return invoke(gpu, node, [array, index, value])


def count(records, address):
    return sum(pointer == address for pointer, size in records)


def test_consecutive_gpu_calls_copy_elements_only_on_host_read(gpu, transfers):
    uploads, downloads = transfers
    array = full((16,), 7)
    assert set_element(gpu, array, 0, 11) is array
    address = array._storage.device.pointer.value
    assert set_element(gpu, array, 1, 22) is array
    assert array._storage.device.pointer.value == address
    assert array.shape == (16,) and array.elements == 16
    assert count(uploads, address) == 1
    assert count(downloads, address) == 0
    assert array.get(0) == 11
    assert array.get(1) == 22
    assert count(downloads, address) == 1
    set_element(gpu, array, 2, 33)
    assert count(uploads, address) == 1
    assert array.get(2) == 33
    assert count(downloads, address) == 2


def test_host_write_uploads_changed_elements_before_next_gpu_call(gpu, transfers):
    uploads, downloads = transfers
    array = full((16,), 7)
    set_element(gpu, array, 0, 11)
    address = array._storage.device.pointer.value
    array.set(1, 42)
    assert count(downloads, address) == 1
    set_element(gpu, array, 2, 22)
    assert count(uploads, address) == 2
    assert array.get(0) == 11
    assert array.get(1) == 42
    assert array.get(2) == 22


def test_full_host_overwrite_does_not_download_old_elements(gpu, transfers):
    uploads, downloads = transfers
    array = full((16,), 7)
    set_element(gpu, array, 0, 11)
    address = array._storage.device.pointer.value
    array.fill(3)
    assert count(downloads, address) == 0
    set_element(gpu, array, 1, 22)
    assert count(uploads, address) == 2
    assert array.get(0) == 3 and array.get(1) == 22


def test_exposed_python_list_alias_remains_coherent(gpu, transfers):
    uploads, _ = transfers
    array = full((16,), 7)
    values = array.data
    set_element(gpu, array, 0, 11)
    address = array._storage.device.pointer.value
    assert values[0] == 11
    values[1] = 42
    set_element(gpu, array, 2, 22)
    assert count(uploads, address) == 2
    assert values[:3] == [11, 42, 22]


def test_gpu_reshape_and_host_reshape_preserve_device_storage(gpu, transfers):
    uploads, downloads = transfers
    array = full((16,), 7)
    set_element(gpu, array, 0, 11)
    address = array._storage.device.pointer.value
    flat_type, matrix_type = LLVMNDArrayType(LLVMInt, 1), LLVMNDArrayType(LLVMInt, 2)
    reshape = function("fun a => NDArray_from_1d2 a 4 4", [flat_type], matrix_type)
    matrix = invoke(gpu, reshape, [array])
    assert matrix.shape == (4, 4)
    flat = matrix.to_1d()
    set_element(gpu, flat, 1, 22)
    assert flat._storage.device.pointer.value == address
    assert count(uploads, address) == 1
    assert count(downloads, address) == 0
    assert flat.get(0) == 11 and flat.get(1) == 22


def test_snapshot_reuses_device_elements_as_pointer_input(gpu, transfers):
    uploads, downloads = transfers
    array = full((16,), 7)
    set_element(gpu, array, 0, 11)
    address = array._storage.device.pointer.value
    snapshot = array.snapshot()
    output = full((1,), 0)
    row_type = LLVMNDArrayType(LLVMInt, 1)
    copy_first = function(
        "fun xs => fun out => NDArray_set1 out 0 (get xs 0)", [LLVMPointerType(LLVMInt), row_type], row_type
    )
    invoke(gpu, copy_first, [snapshot, output])
    assert count(uploads, address) == 1
    assert count(downloads, address) == 0
    assert len(snapshot) == 16
    assert output.get(0) == 11
    assert snapshot[0] == 11
    assert count(downloads, address) == 1
    with pytest.raises(ValueError, match="ownership"):
        array.get(0)


def test_cpu_kernel_materializes_then_gpu_uploads_its_changes(gpu, transfers):
    uploads, downloads = transfers
    array = full((16,), 7)
    set_element(gpu, array, 0, 11)
    address = array._storage.device.pointer.value
    ty = LLVMNDArrayType(LLVMInt, 1)
    node = function("fun a => NDArray_set1 a 1 42", [ty], ty)
    code = CPULLVMIRGenerator().generate_ir([node])
    assert CPULLVMExecutionEngine().execute(code, "lazy_test", [array], [ty], ty) is array
    assert count(downloads, address) == 1
    set_element(gpu, array, 2, 22)
    assert count(uploads, address) == 2
    assert array.get(0) == 11 and array.get(1) == 42 and array.get(2) == 22


def test_discard_releases_storage_without_copying_back(gpu, transfers):
    _, downloads = transfers
    array = full((16,), 7)
    set_element(gpu, array, 0, 11)
    address = array._storage.device.pointer.value
    array.discard()
    gc.collect()
    assert count(downloads, address) == 0
    if isinstance(gpu.libcuda, EmulatedCUDA):
        assert address not in gpu.libcuda.allocations


def test_engine_close_materializes_live_arrays(gpu):
    array = full((16,), 7)
    set_element(gpu, array, 0, 11)
    gpu.close()
    assert array._storage.device is None
    assert array.get(0) == 11
    set_element(gpu, array, 1, 22)
    assert array.get(0) == 11 and array.get(1) == 22


def test_kernel_error_releases_persistent_buffers_and_preserves_data(gpu):
    array = full((16,), 7)
    set_element(gpu, array, 0, 11)
    with pytest.raises(IndexError, match="out of bounds"):
        set_element(gpu, array, 16, 99)
    assert array._storage.device is None
    assert array.get(0) == 11
    set_element(gpu, array, 1, 22)
    assert array.get(0) == 11 and array.get(1) == 22


def test_migrating_between_cuda_contexts_preserves_latest_values():
    first, second = emulated_engine(), emulated_engine()
    array = full((16,), 7)
    try:
        set_element(first, array, 0, 11)
        set_element(second, array, 1, 22)
        assert not first.libcuda.allocations
        assert array.get(0) == 11 and array.get(1) == 22
    finally:
        first.close()
        second.close()
    assert not second.libcuda.allocations


def test_cpu_reads_device_snapshot(gpu, transfers):
    _, downloads = transfers
    array = full((16,), 7)
    set_element(gpu, array, 0, 11)
    address = array._storage.device.pointer.value
    snapshot, output = array.snapshot(), full((1,), 0)
    row_type = LLVMNDArrayType(LLVMInt, 1)
    node = function(
        "fun xs => fun out => NDArray_set1 out 0 (get xs 0)", [LLVMPointerType(LLVMInt), row_type], row_type
    )
    code = CPULLVMIRGenerator().generate_ir([node])
    result = CPULLVMExecutionEngine().execute(code, "lazy_test", [snapshot, output], node.arg_types, row_type)
    assert result.get(0) == 11
    assert count(downloads, address) == 1


def test_failed_upload_releases_allocation_and_can_retry(gpu, monkeypatch):
    array = full((16,), 7)
    with monkeypatch.context() as patch:
        patch.setattr(gpu.libcuda, "cuMemcpyHtoD_v2", lambda *args: 1)
        with pytest.raises(CUDAExecutionError, match="cuMemcpyHtoD"):
            set_element(gpu, array, 0, 11)
    assert array._storage.device is None
    if isinstance(gpu.libcuda, EmulatedCUDA):
        assert not gpu.libcuda.allocations
    assert array.get(0) == 7
    set_element(gpu, array, 0, 11)
    assert array.get(0) == 11


def test_failed_launch_keeps_preceding_gpu_results(gpu, monkeypatch):
    array = full((16,), 7)
    set_element(gpu, array, 0, 11)
    with monkeypatch.context() as patch:
        patch.setattr(gpu.libcuda, "cuLaunchKernel", lambda *args: 1)
        with pytest.raises(CUDAExecutionError, match="cuLaunchKernel"):
            set_element(gpu, array, 1, 22)
    assert array._storage.device is None
    assert array.get(0) == 11 and array.get(1) == 7
    if isinstance(gpu.libcuda, EmulatedCUDA):
        assert not gpu.libcuda.allocations


def test_failed_host_download_can_retry(gpu, monkeypatch):
    array = full((16,), 7)
    set_element(gpu, array, 0, 11)
    with monkeypatch.context() as patch:
        patch.setattr(gpu.libcuda, "cuMemcpyDtoH_v2", lambda *args: 1)
        with pytest.raises(CUDAExecutionError, match="cuMemcpyDtoH"):
            array.get(0)
    assert array.get(0) == 11


def test_unrecoverable_failure_does_not_expose_stale_host_elements(monkeypatch):
    engine = emulated_engine()
    array = full((16,), 7)
    set_element(engine, array, 0, 11)
    with monkeypatch.context() as patch:
        patch.setattr(engine.libcuda, "cuCtxSynchronize", lambda: 1)
        patch.setattr(engine.libcuda, "cuMemcpyDtoH_v2", lambda *args: 1)
        with pytest.raises(CUDAExecutionError, match="cuCtxSynchronize"):
            set_element(engine, array, 1, 22)
    assert not engine.libcuda.allocations
    with pytest.raises(RuntimeError, match="GPU execution failure"):
        array.get(0)
    array.fill(3)
    set_element(engine, array, 0, 11)
    assert array.get(0) == 11 and array.get(1) == 3
    engine.close()


def set_managed_element(gpu, array, index, value):
    ty = LLVMPointerType(LLVMInt)
    node = function("fun a => fun i => fun v => set a i v", [ty, LLVMInt, LLVMInt], ty)
    return invoke(gpu, node, [array, index, value])


def test_managed_arrays_reuse_device_storage_and_synchronize_list_access(gpu, transfers):
    uploads, downloads = transfers
    array = ManagedArray([7] * 16)
    assert set_managed_element(gpu, array, 0, 11) is array
    address = array._storage.device.pointer.value
    assert set_managed_element(gpu, array, 1, 22) is array
    assert len(array) == 16
    assert count(uploads, address) == 1 and count(downloads, address) == 0
    assert array[:3] == [11, 22, 7]
    assert count(downloads, address) == 1
    array[2] = 42
    set_managed_element(gpu, array, 3, 33)
    assert count(uploads, address) == 2
    assert list(array[:4]) == [11, 22, 42, 33]


def test_managed_array_host_resize_and_cpu_transition(gpu):
    array = ManagedArray([7] * 16)
    set_managed_element(gpu, array, 0, 11)
    array.append(42)
    set_managed_element(gpu, array, 1, 22)
    assert len(array) == 17 and array[-1] == 42
    ty = LLVMPointerType(LLVMInt)
    node = function("fun a => set a 2 99", [ty], ty)
    code = CPULLVMIRGenerator().generate_ir([node])
    assert CPULLVMExecutionEngine().execute(code, "lazy_test", [array], [ty], ty) is array
    set_managed_element(gpu, array, 3, 33)
    assert array[:4] == [11, 22, 99, 33]


def test_array_ndarray_bridge_retains_device_allocation(gpu, transfers):
    uploads, downloads = transfers
    array = ManagedArray([7] * 16)
    set_managed_element(gpu, array, 0, 11)
    address = array._storage.device.pointer.value
    matrix = from_array(array).from_1d2(4, 4)
    flat = matrix.to_1d()
    set_element(gpu, flat, 1, 22)
    result = flat.to_array()
    assert result is array
    set_managed_element(gpu, result, 2, 33)
    assert result._storage.device.pointer.value == address
    assert count(uploads, address) == 1 and count(downloads, address) == 0
    assert result[:3] == [11, 22, 33]


def test_cpu_call_updates_ndarray_when_returning_managed_array(gpu):
    array = ManagedArray([7] * 16)
    matrix = full((16,), 7)
    set_managed_element(gpu, array, 0, 11)
    set_element(gpu, matrix, 0, 22)
    pointer = LLVMPointerType(LLVMInt)
    ndarray = LLVMNDArrayType(LLVMInt, 1)
    node = function("fun a => fun b => let changed = NDArray_set1 b 1 42 in set a 1 33", [pointer, ndarray], pointer)
    code = CPULLVMIRGenerator().generate_ir([node])
    assert CPULLVMExecutionEngine().execute(code, "lazy_test", [array, matrix], [pointer, ndarray], pointer) is array
    set_element(gpu, matrix, 2, 99)
    assert array[:2] == [11, 33]
    assert matrix.get(0) == 22 and matrix.get(1) == 42 and matrix.get(2) == 99


def test_read_only_cpu_call_does_not_force_reupload(gpu, transfers):
    uploads, _ = transfers
    array = full((16,), 7)
    set_element(gpu, array, 0, 11)
    address = array._storage.device.pointer.value
    ty = LLVMNDArrayType(LLVMInt, 1)
    node = function("fun a => a", [ty], ty)
    code = CPULLVMIRGenerator().generate_ir([node])
    assert CPULLVMExecutionEngine().execute(code, "lazy_test", [array], [ty], ty) is array
    set_element(gpu, array, 1, 22)
    assert count(uploads, address) == 1
    assert array.get(0) == 11 and array.get(1) == 22


def test_managed_array_python_and_numpy_readers_see_gpu_results(gpu):
    np = pytest.importorskip("numpy")
    array = ManagedArray([7] * 16)
    set_managed_element(gpu, array, 0, 11)
    assert np.asarray(array).tolist() == [11] + [7] * 15
    set_managed_element(gpu, array, 1, 22)
    assert sum(array) == 11 + 22 + 7 * 14
    assert repr(array).startswith("[11, 22,")
    assert array.copy() == [11, 22] + [7] * 14
    assert [0] + array == [0, 11, 22] + [7] * 14
    array.reverse()
    assert array[-2:] == [22, 11]
    array.clear()
    assert len(array) == 0


def test_aeon_array_gpu_calls_are_managed_automatically(gpu, monkeypatch, capsys):
    def initialize(pipeline):
        pipeline.cuda_initialized = True
        pipeline.register_backend("cuda", Backend(gpu, CUDALLVMIRGenerator(), CUDALLVMLowerer()))

    if isinstance(gpu.libcuda, EmulatedCUDA):
        gpu.libcuda.param_types = [ctypes.c_void_p, ctypes.c_int32, ctypes.c_void_p]
    monkeypatch.setattr(MultiBackendPipeline, "_initialize_cuda_backend", initialize)
    uploads, downloads = [], []
    upload, download = gpu.libcuda.cuMemcpyHtoD_v2, gpu.libcuda.cuMemcpyDtoH_v2

    def record_upload(destination, source, size):
        uploads.append(size)
        return upload(destination, source, size)

    def record_download(destination, source, size):
        downloads.append(size)
        return download(destination, source, size)

    monkeypatch.setattr(gpu.libcuda, "cuMemcpyHtoD_v2", record_upload)
    monkeypatch.setattr(gpu.libcuda, "cuMemcpyDtoH_v2", record_download)
    source = """open Array
@gpu
def write (1 a:{r:(Array Int) | r.size = 16}) (v:Int) : {r:(Array Int) | r.size = 16} :=
    a.set 0 v;
def main (args:Int) : Unit :=
    let 1 a:{r:(Array Int) | r.size = 16} := native "[7] * 16" in
    let 1 b := write a 11 in
    let 1 c := write b 22 in
    print (c.get 0);
"""
    driver = AeonDriver(AeonConfig(synthesizer="none", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0))
    assert not driver.parse(aeon_code=source)
    driver.run()
    assert capsys.readouterr().out.strip() == "22"
    assert uploads.count(16 * 4) == 1
    assert downloads.count(16 * 4) == 1


@pytest.mark.parametrize(
    "filename,payload_bytes,upload_count",
    [("nbody.ae", 257 * 7 * 4, 11), ("floyd_warshall.ae", 4 * 4 * 4, 5), ("lazy_copy.ae", 17 * 33 * 4, 1)],
)
def test_parallel_examples_download_only_the_final_state(
    real_cuda, monkeypatch, capsys, filename, payload_bytes, upload_count
):
    uploads, downloads = [], []
    upload, download = real_cuda.libcuda.cuMemcpyHtoD_v2, real_cuda.libcuda.cuMemcpyDtoH_v2

    def record_upload(destination, source, size):
        uploads.append(size)
        return upload(destination, source, size)

    def record_download(destination, source, size):
        downloads.append(size)
        return download(destination, source, size)

    def initialize(pipeline):
        pipeline.cuda_initialized = True
        pipeline.register_backend("cuda", Backend(real_cuda, CUDALLVMIRGenerator(), CUDALLVMLowerer()))

    monkeypatch.setattr(real_cuda.libcuda, "cuMemcpyHtoD_v2", record_upload)
    monkeypatch.setattr(real_cuda.libcuda, "cuMemcpyDtoH_v2", record_download)
    monkeypatch.setattr(MultiBackendPipeline, "_initialize_cuda_backend", initialize)
    path = Path(__file__).resolve().parents[1] / "examples/llvm/gpu" / filename
    driver = AeonDriver(AeonConfig(synthesizer="none", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0))
    assert not driver.parse(aeon_code=path.read_text())
    driver.run()
    expected = {"nbody.ae": -1.951089859, "floyd_warshall.ae": 9.0, "lazy_copy.ae": 42.0}
    assert float(capsys.readouterr().out.strip()) == pytest.approx(expected[filename])
    assert uploads.count(payload_bytes) == upload_count
    assert downloads.count(payload_bytes) == 1
    real_cuda.close()
