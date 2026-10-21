"""Stable, dynamic-length selection through the existing filter AST and CUDA pipeline."""

from pathlib import Path
import ctypes

import llvmlite.binding as llvm
import pytest

from aeon.bindings.ndarray import NDArray, ManagedArray, full
from aeon.core.parser import parse_term
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.llvm.core import Backend
from aeon.llvm.cuda.converter import CUDALLVMIRGenerator
from aeon.llvm.cuda.executor import CUDAExecutionEngine, CUDAExecutionError
from aeon.llvm.cuda.lowerer import CUDALLVMLowerer
from aeon.llvm.filter import FilterLaunch
from aeon.llvm.llvm_ast import (
    LLVMFunctionType,
    LLVMInt,
    LLVMFloat,
    LLVMDouble,
    LLVMLong,
    LLVMBool,
    LLVMNDArrayType,
    LLVMPointerType,
    LLVMVectorFilter,
)
from aeon.llvm.pipeline import MultiBackendPipeline
from aeon.llvm.ndarray import NDArrayDescriptor
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.name import Name
from tests.cuda_reduction_test import backend as backend, cuda as cuda


def compile_filter(backend, body, types, result):
    backend.generator = type(backend.generator)()
    node = backend.lowerer.lower(parse_term(body), expected_type=LLVMFunctionType(types, result))
    node.name = Name("filter_test", 0)
    code = backend.generator.generate_ir([node])
    llvm.parse_assembly(code).verify()
    selection = backend.generator.filter_launches["filter_test"]
    return node, code, selection


def execute(backend, body, arguments, types, result):
    node, code, selection = compile_filter(backend, body, types, result)
    return backend.executor.execute(
        code,
        "filter_test",
        arguments,
        node.arg_types,
        result,
        filter_input=(selection.array_index, selection.count(arguments)),
    )


@pytest.mark.parametrize("size", [0, 1, 17, 256, 257, 65537])
@pytest.mark.parametrize(
    "predicate,reference",
    [
        ("fun x => x % 3 == 0", lambda x: x % 3 == 0),
        ("fun x => true", lambda x: True),
        ("fun x => false", lambda x: False),
    ],
)
def test_stable_parallel_filter(backend, size, predicate, reference):
    values = [(i * 17 % 97) - 48 for i in range(size)]
    array = NDArray(values.copy(), (size,))
    ty = LLVMNDArrayType(LLVMInt, 1)
    result = execute(backend, f"fun a => NDArray_filter a ({predicate})", [array], [ty], ty)
    assert result is array
    assert result.data == [value for value in values if reference(value)]
    assert result.shape == (len(result.data),)


@pytest.mark.parametrize("shape", [(3, 5), (3, 2, 5), (0, 3)])
def test_filter_flattens_ranked_arrays_in_row_major_order(backend, shape):
    array = full(shape, 3)
    ty = LLVMNDArrayType(LLVMInt, len(shape))
    result = execute(backend, "fun a => NDArray_filter a (fun x => x > 0)", [array], [ty], LLVMNDArrayType(LLVMInt, 1))
    assert result.shape == (len(result.data),) and all(value == 3 for value in result.data)


@pytest.mark.parametrize(
    "element,values,predicate,expected",
    [
        (LLVMFloat, [-1.25, 0.0, 1.5, 3.75], "fun x => x > 0.0", [1.5, 3.75]),
        (LLVMDouble, [-1.25, 0.0, 1.5, 3.75], "fun x => x > 0.0", [1.5, 3.75]),
        (LLVMLong, [-(2**35), 0, 2**35], "fun x => x > 0", [2**35]),
        (LLVMBool, [True, False, False, True], "fun x => x", [True, True]),
    ],
)
def test_filter_scalar_types(backend, element, values, predicate, expected):
    ty = LLVMNDArrayType(element, 1)
    array = NDArray(values.copy(), (len(values),))
    result = execute(backend, f"fun a => NDArray_filter a ({predicate})", [array], [ty], ty)
    assert result.data == expected


@pytest.mark.parametrize("managed", [False, True])
@pytest.mark.parametrize("element,value,name", [(LLVMInt, 3, "filter_n_int"), (LLVMFloat, 1.25, "filter_n_float")])
def test_sized_array_filter_returns_exact_length_and_preserves_identity(backend, managed, element, value, name):
    values = [value, -value, value, -value] * 129
    array = ManagedArray(values) if managed else values.copy()
    ty = LLVMPointerType(element)
    zero = "0.0" if element == LLVMFloat else "0"
    result = execute(backend, f"fun a => fun n => {name} (fun x => x > {zero}) a n", [array, 257], [ty, LLVMInt], ty)
    assert result is array
    assert result == [value] * 129


def test_predicate_captures_a_scalar_parameter(backend):
    values = list(range(1025))
    array = NDArray(values.copy(), (len(values),))
    ty = LLVMNDArrayType(LLVMInt, 1)
    result = execute(
        backend, "fun a => fun cutoff => NDArray_filter a (fun x => x > cutoff)", [array, 511], [ty, LLVMInt], ty
    )
    assert result.data == values[512:]


def test_predicate_calls_a_compiled_helper(backend):
    helper = backend.lowerer.lower(parse_term("fun x => x > 10"), expected_type=LLVMFunctionType([LLVMInt], LLVMBool))
    helper.name = Name("keep_large", 0)
    ty = LLVMNDArrayType(LLVMInt, 1)
    node = backend.lowerer.lower(
        parse_term("fun a => NDArray_filter a (fun x => keep_large x)"),
        expected_type=LLVMFunctionType([ty], ty),
        type_env={helper.name: helper.type},
        env={helper.name: helper},
    )
    node.name = Name("filter_helper", 0)
    code = backend.generator.generate_ir([helper, node])
    llvm.parse_assembly(code).verify()
    array = NDArray(list(range(513)), (513,))
    result = backend.executor.execute(code, "filter_helper", [array], [ty], ty, filter_input=(0, 513))
    assert result.data == list(range(11, 513))


@pytest.mark.parametrize("count", [-1, 17, True, 3.0])
def test_filter_validates_source_length(count):
    with pytest.raises(ValueError, match="Filter length"):
        FilterLaunch(0, size_index=1).count([[0] * 16, count])


def test_scan_compiles_to_nvptx_without_a_gpu():
    backend = Backend(None, CUDALLVMIRGenerator(), CUDALLVMLowerer())
    ty = LLVMNDArrayType(LLVMInt, 1)
    node, code, _ = compile_filter(backend, "fun a => NDArray_filter a (fun x => x > 0)", [ty], ty)
    assert isinstance(node.body, LLVMVectorFilter)
    assert "addrspace(3)" in code and "llvm.nvvm.barrier0" in code
    assert '__scan"' in code and '__offsets"' in code and '__scatter"' in code
    engine = CUDAExecutionEngine.__new__(CUDAExecutionEngine)
    assert "bar.sync" in engine._compile_to_ptx(code)


@pytest.mark.parametrize("managed", [False, True])
def test_filter_filter_reduce_keeps_elements_on_gpu(cuda, monkeypatch, managed):
    uploads, downloads, launches = [], [], []
    upload, download, launch = cuda.libcuda.cuMemcpyHtoD_v2, cuda.libcuda.cuMemcpyDtoH_v2, cuda.libcuda.cuLaunchKernel

    def record_upload(destination, source, size):
        uploads.append(size)
        return upload(destination, source, size)

    def record_download(destination, source, size):
        downloads.append(size)
        return download(destination, source, size)

    def record_launch(function, gx, gy, gz, bx, by, bz, shared, stream, parameters, extra):
        launches.append((gx, bx))
        return launch(function, gx, gy, gz, bx, by, bz, shared, stream, parameters, extra)

    monkeypatch.setattr(cuda.libcuda, "cuMemcpyHtoD_v2", record_upload)
    monkeypatch.setattr(cuda.libcuda, "cuMemcpyDtoH_v2", record_download)
    monkeypatch.setattr(cuda.libcuda, "cuLaunchKernel", record_launch)
    backend = Backend(cuda, CUDALLVMIRGenerator(), CUDALLVMLowerer())
    array = ManagedArray(range(1025)) if managed else NDArray(list(range(1025)), (1025,))
    ty = LLVMPointerType(LLVMInt) if managed else LLVMNDArrayType(LLVMInt, 1)
    first = (
        "fun a => fun n => filter_n_int (fun x => x % 2 == 0) a n"
        if managed
        else "fun a => fun n => NDArray_filter a (fun x => x % 2 == 0)"
    )
    second = (
        "fun a => fun n => filter_n_int (fun x => x > 512) a n"
        if managed
        else "fun a => fun n => NDArray_filter a (fun x => x > 512)"
    )
    assert execute(backend, first, [array, 1025], [ty, LLVMInt], ty) is array
    assert execute(backend, second, [array, 513], [ty, LLVMInt], ty) is array
    assert len(array) == 256 if managed else array.shape == (256,)
    backend.generator = CUDALLVMIRGenerator()
    source = (
        "fun a => reduce_n_int (fun acc => fun x => acc + x) 0 a 256"
        if managed
        else "fun a => NDArray_reduce a (fun acc => fun x => acc + x) 0"
    )
    node = backend.lowerer.lower(parse_term(source), expected_type=LLVMFunctionType([ty], LLVMInt))
    node.name = Name("after_filter", 0)
    code = backend.generator.generate_ir([node])
    assert cuda.execute(code, "after_filter", [array], node.arg_types, LLVMInt, reduction_count=256) == sum(
        range(514, 1025, 2)
    )
    assert uploads.count(1025 * 4) == 1 and all(size in {4, ctypes.sizeof(NDArrayDescriptor)} for size in downloads)
    assert not array._storage.host_current
    assert launches[:3] == [(5, 256), (1, 256), (5, 256)]
    array.discard() if not managed else cuda.close()


def test_empty_result_can_be_reduced_without_host_access(cuda):
    backend = Backend(cuda, CUDALLVMIRGenerator(), CUDALLVMLowerer())
    ty = LLVMNDArrayType(LLVMInt, 1)
    array = full((513,), 7)
    execute(backend, "fun a => NDArray_filter a (fun x => false)", [array], [ty], ty)
    assert array.shape == (0,) and not array._storage.host_current
    node = backend.lowerer.lower(
        parse_term("fun a => NDArray_reduce a (fun acc => fun x => acc + x) 5"),
        expected_type=LLVMFunctionType([ty], LLVMInt),
    )
    node.name = Name("empty_sum", 0)
    code = CUDALLVMIRGenerator().generate_ir([node])
    assert cuda.execute(code, "empty_sum", [array], [ty], LLVMInt, reduction_count=0) == 5
    assert array.data == []
    cuda.close()


@pytest.mark.parametrize("failure", ["scan_allocation", "scan_launch", "scatter_launch", "length_download"])
def test_failed_filter_releases_temporary_and_resident_buffers(cuda, monkeypatch, failure):
    allocations = set()
    allocate, release = cuda.libcuda.cuMemAlloc_v2, cuda.libcuda.cuMemFree_v2
    launch, download = cuda.libcuda.cuLaunchKernel, cuda.libcuda.cuMemcpyDtoH_v2
    allocation_count, launch_count = 0, 0

    def record_allocate(destination, size):
        nonlocal allocation_count
        allocation_count += 1
        if failure == "scan_allocation" and allocation_count == 6:
            return 2
        rc = allocate(destination, size)
        if rc == 0:
            allocations.add(ctypes.cast(destination, ctypes.POINTER(ctypes.c_uint64))[0])
        return rc

    def record_release(address):
        rc = release(address)
        if rc == 0:
            allocations.remove(address)
        return rc

    def fail_launch(*args):
        nonlocal launch_count
        launch_count += 1
        if (failure == "scan_launch" and launch_count == 2) or (failure == "scatter_launch" and launch_count == 5):
            return 1
        return launch(*args)

    def fail_download(destination, source, size):
        return 1 if failure == "length_download" and size == 4 else download(destination, source, size)

    monkeypatch.setattr(cuda.libcuda, "cuMemAlloc_v2", record_allocate)
    monkeypatch.setattr(cuda.libcuda, "cuMemFree_v2", record_release)
    monkeypatch.setattr(cuda.libcuda, "cuLaunchKernel", fail_launch)
    monkeypatch.setattr(cuda.libcuda, "cuMemcpyDtoH_v2", fail_download)
    backend = Backend(cuda, CUDALLVMIRGenerator(), CUDALLVMLowerer())
    array = full((65537,), 7)
    ty = LLVMNDArrayType(LLVMInt, 1)
    with pytest.raises(CUDAExecutionError, match="filter"):
        execute(backend, "fun a => NDArray_filter a (fun x => x > 0)", [array], [ty], ty)
    assert not allocations
    assert array.shape == (65537,) and array.get(0) == 7 and array._storage.device is None


@pytest.mark.parametrize("mode", ["interpreted", "cpu", "cuda"])
def test_runnable_filter_then_reduce(mode, request, monkeypatch, capsys):
    if mode == "cuda":
        engine = request.getfixturevalue("cuda")

        def initialize(pipeline):
            pipeline.cuda_initialized = True
            pipeline.register_backend("cuda", Backend(engine, CUDALLVMIRGenerator(), CUDALLVMLowerer()))

        monkeypatch.setattr(MultiBackendPipeline, "_initialize_cuda_backend", initialize)
    source = (Path(__file__).resolve().parents[1] / "examples/llvm/gpu/filter.ae").read_text()
    if mode == "interpreted":
        source = source.replace("@gpu\n", "")
    elif mode == "cpu":
        source = source.replace("@gpu\n", "@llvm\n")
    driver = AeonDriver(AeonConfig(synthesizer="none", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0))
    assert not driver.parse(aeon_code=source)
    driver.run()
    assert capsys.readouterr().out.strip() == "262656"
