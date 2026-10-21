"""Lambda reductions share one lowering node and execute a multi-block CUDA tree."""

import ctypes
from pathlib import Path

import llvmlite.binding as llvm
import pytest

from aeon.bindings.ndarray import NDArray, ManagedArray, full
from aeon.core.parser import parse_term
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.llvm.core import Backend
from aeon.llvm.cpu.converter import CPULLVMIRGenerator
from aeon.llvm.cpu.executor import CPULLVMExecutionEngine
from aeon.llvm.cpu.lowerer import CPULLVMLowerer
from aeon.llvm.cuda.converter import CUDALLVMIRGenerator
from aeon.llvm.cuda.executor import CUDAExecutionEngine, CUDAExecutionError
from aeon.llvm.cuda.lowerer import CUDALLVMLowerer
from aeon.llvm.cuda.reduction import ReductionLaunch
from aeon.llvm.llvm_ast import (
    LLVMFunctionType,
    LLVMInt,
    LLVMFloat,
    LLVMDouble,
    LLVMLong,
    LLVMBool,
    LLVMNDArrayType,
    LLVMPointerType,
    LLVMVectorReduce,
)
from aeon.llvm.pipeline import MultiBackendPipeline
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.name import Name


@pytest.fixture(scope="module")
def cuda():
    try:
        engine = CUDAExecutionEngine()
    except CUDAExecutionError as error:
        pytest.skip(str(error))
    yield engine
    engine.close()


@pytest.fixture(params=["cpu", "cuda"])
def backend(request):
    if request.param == "cuda":
        result = Backend(request.getfixturevalue("cuda"), CUDALLVMIRGenerator(), CUDALLVMLowerer())
    else:
        result = Backend(CPULLVMExecutionEngine(), CPULLVMIRGenerator(), CPULLVMLowerer())
    yield result
    if request.param == "cuda":
        result.executor.close()


def compile_reduction(backend, body, types, result):
    node = backend.lowerer.lower(parse_term(body), expected_type=LLVMFunctionType(types, result))
    node.name = Name("reduce_test", 0)
    code = backend.generator.generate_ir([node])
    llvm.parse_assembly(code).verify()
    return node, code


def execute(backend, body, arguments, types, result):
    node, code = compile_reduction(backend, body, types, result)
    launch = getattr(backend.generator, "reduction_launches", {}).get("reduce_test")
    if isinstance(backend.executor, CUDAExecutionEngine):
        assert launch is not None
    return backend.executor.execute(
        code,
        "reduce_test",
        arguments,
        node.arg_types,
        result,
        reduction_count=launch.count(arguments) if launch is not None else None,
    )


OPERATIONS = [
    ("fun acc => fun x => acc + x", 19, lambda values: 19 + sum(values)),
    ("fun acc => fun x => if acc < x then acc else x", 200, lambda values: min([200, *values])),
    ("fun acc => fun x => if acc > x then acc else x", -200, lambda values: max([-200, *values])),
]


@pytest.mark.parametrize("size", [0, 1, 17, 256, 257, 65537])
@pytest.mark.parametrize("combiner,initial,reference", OPERATIONS)
def test_parallel_sum_min_max(backend, size, combiner, initial, reference):
    values = [(i * 17 % 97) - 48 for i in range(size)]
    array = NDArray(values, (size,))
    ty = LLVMNDArrayType(LLVMInt, 1)
    result = execute(
        backend, f"fun a => fun z => NDArray_reduce a ({combiner}) z", [array, initial], [ty, LLVMInt], LLVMInt
    )
    assert result == reference(values)


@pytest.mark.parametrize("element,value", [(LLVMFloat, -1.25), (LLVMDouble, -1.25), (LLVMLong, 2**35)])
def test_reduction_preserves_element_type(backend, element, value):
    ty = LLVMNDArrayType(element, 2)
    array = full((17, 33), value)
    result = execute(
        backend,
        "fun a => fun z => NDArray_reduce a (fun acc => fun x => acc + x) z",
        [array, value],
        [ty, element],
        element,
    )
    assert result == pytest.approx(value * (17 * 33 + 1))


@pytest.mark.parametrize("element", [LLVMFloat, LLVMDouble])
@pytest.mark.parametrize("combiner,initial,reference", OPERATIONS[1:])
def test_floating_point_min_max(backend, element, combiner, initial, reference):
    values = [(i % 91 - 45) * 1.25 for i in range(513)]
    ty = LLVMNDArrayType(element, 1)
    array = NDArray(values, (len(values),))
    result = execute(
        backend, f"fun a => fun z => NDArray_reduce a ({combiner}) z", [array, initial], [ty, element], element
    )
    assert result == reference(values)


@pytest.mark.parametrize("op,initial,expected", [("&&", True, False), ("||", False, True)])
def test_boolean_reduction(backend, op, initial, expected):
    ty = LLVMNDArrayType(LLVMBool, 1)
    array = NDArray([True] * 512 + [False], (513,))
    assert (
        execute(
            backend,
            f"fun a => fun z => NDArray_reduce a (fun acc => fun x => acc {op} x) z",
            [array, initial],
            [ty, LLVMBool],
            LLVMBool,
        )
        == expected
    )


@pytest.mark.parametrize("shape", [(2, 3, 5), (0, 7, 3)])
def test_reduction_of_rank_three_arrays(backend, shape):
    ty = LLVMNDArrayType(LLVMInt, 3)
    array = full(shape, 7)
    assert (
        execute(backend, "fun a => NDArray_reduce a (fun acc => fun x => acc + x) 5", [array], [ty], LLVMInt)
        == 5 + 7 * array.elements
    )


def test_lambda_captures_and_initial_value_are_applied_once(backend):
    ty = LLVMNDArrayType(LLVMInt, 1)
    array = full((65537,), 1)
    # a + b + bias is associative. There are N combines, including the seed.
    result = execute(
        backend,
        "fun a => fun bias => NDArray_reduce a (fun acc => fun x => acc + x + bias) 5",
        [array, 3],
        [ty, LLVMInt],
        LLVMInt,
    )
    assert result == 5 + 4 * array.elements


def test_lambda_can_call_an_ordinary_compiled_helper(backend):
    helper = backend.lowerer.lower(
        parse_term("fun x => fun y => x + y"), expected_type=LLVMFunctionType([LLVMInt, LLVMInt], LLVMInt)
    )
    helper.name = Name("combine", 0)
    ty = LLVMNDArrayType(LLVMInt, 1)
    node = backend.lowerer.lower(
        parse_term("fun a => fun bias => NDArray_reduce a (fun acc => fun x => combine acc x + bias) 5"),
        expected_type=LLVMFunctionType([ty, LLVMInt], LLVMInt),
        type_env={helper.name: helper.type},
        env={helper.name: helper},
    )
    node.name = Name("with_helper", 0)
    code = backend.generator.generate_ir([helper, node])
    llvm.parse_assembly(code).verify()
    launch = getattr(backend.generator, "reduction_launches", {}).get("with_helper")
    if isinstance(backend.executor, CUDAExecutionEngine):
        assert launch is not None
    assert (
        backend.executor.execute(
            code,
            "with_helper",
            [full((513,), 1), 3],
            node.arg_types,
            LLVMInt,
            reduction_count=513 if launch else None,
        )
        == 2057
    )


def test_heterogeneous_accumulator_retains_sequential_fold(backend):
    array = ManagedArray([1.25] * 513)
    ty = LLVMPointerType(LLVMFloat)
    node, code = compile_reduction(
        backend,
        "fun a => fun n => fun z => reduce (fun acc => fun x => acc + 1) z a n",
        [ty, LLVMInt, LLVMLong],
        LLVMLong,
    )
    assert not getattr(backend.generator, "reduction_launches", {})
    assert backend.executor.execute(code, "reduce_test", [array, 513, 2**35], node.arg_types, LLVMLong) == 2**35 + 513


def test_associative_noncommutative_lambda_preserves_element_order(backend):
    values = [0] * 257 + [11, 22, 33] + [0] * 511
    array = NDArray(values, (len(values),))
    ty = LLVMNDArrayType(LLVMInt, 1)
    result = execute(
        backend, "fun a => NDArray_reduce a (fun acc => fun x => if acc == 0 then x else acc) 0", [array], [ty], LLVMInt
    )
    assert result == 11


@pytest.mark.parametrize("element,value,name", [(LLVMInt, 3, "reduce_n_int"), (LLVMFloat, 1.25, "reduce_n_float")])
def test_existing_sized_array_reductions_use_the_same_tree(backend, element, value, name):
    array = ManagedArray([value] * 513)
    ty = LLVMPointerType(element)
    assert execute(
        backend,
        f"fun a => fun n => fun z => {name} (fun acc => fun x => acc + x) z a n",
        [array, 257, value],
        [ty, LLVMInt, element],
        element,
    ) == pytest.approx(value * 258)


def test_generated_cuda_uses_shared_tree_and_compiles_the_lambda():
    backend = Backend(None, CUDALLVMIRGenerator(), CUDALLVMLowerer())
    ty = LLVMNDArrayType(LLVMInt, 1)
    node, code = compile_reduction(
        backend, "fun a => NDArray_reduce a (fun acc => fun x => if acc < x then acc else x) 999", [ty], LLVMInt
    )
    assert isinstance(node.body, LLVMVectorReduce)
    assert backend.generator.reduction_launches["reduce_test"] == ReductionLaunch(0)
    assert "addrspace(3)" in code and "llvm.nvvm.barrier0" in code
    assert 'define void @"reduce_test__reduce"' in code
    # NVPTX code generation is checked even on hosts without a CUDA device.
    engine = CUDAExecutionEngine.__new__(CUDAExecutionEngine)
    ptx = engine._compile_to_ptx(code)
    assert "bar.sync" in ptx and "min.s32" in ptx


@pytest.mark.parametrize("size", [-1, 17, 2.0, True])
def test_launch_rejects_invalid_lengths(size):
    with pytest.raises(ValueError, match="Reduction length"):
        ReductionLaunch(0, size_index=1).count([[0] * 16, size])


def test_reduction_reuses_dirty_gpu_storage_without_element_copies(cuda, monkeypatch):
    ty = LLVMNDArrayType(LLVMInt, 1)
    fill_backend = Backend(cuda, CUDALLVMIRGenerator(), CUDALLVMLowerer())
    fill_node = fill_backend.lowerer.lower(
        parse_term("fun a => NDArray_fill a 3"), expected_type=LLVMFunctionType([ty], ty)
    )
    fill_node.name = Name("fill_source", 0)
    fill_code = fill_backend.generator.generate_ir([fill_node])
    array = full((1025,), 7)
    cuda.execute(fill_code, "fill_source", [array], [ty], ty, launch_shape=array.shape)
    address = array._storage.device.pointer.value
    uploads, downloads, launches = [], [], []
    upload, download, launch = cuda.libcuda.cuMemcpyHtoD_v2, cuda.libcuda.cuMemcpyDtoH_v2, cuda.libcuda.cuLaunchKernel

    def record_upload(destination, source, size):
        uploads.append(destination)
        return upload(destination, source, size)

    def record_download(destination, source, size):
        downloads.append((source, size))
        return download(destination, source, size)

    def record_launch(function, gx, gy, gz, bx, by, bz, shared, stream, params, extra):
        launches.append((gx, bx))
        return launch(function, gx, gy, gz, bx, by, bz, shared, stream, params, extra)

    monkeypatch.setattr(cuda.libcuda, "cuMemcpyHtoD_v2", record_upload)
    monkeypatch.setattr(cuda.libcuda, "cuMemcpyDtoH_v2", record_download)
    monkeypatch.setattr(cuda.libcuda, "cuLaunchKernel", record_launch)
    backend = Backend(cuda, CUDALLVMIRGenerator(), CUDALLVMLowerer())
    assert execute(backend, "fun a => NDArray_reduce a (fun acc => fun x => acc + x) 0", [array], [ty], LLVMInt) == 3075
    assert launches == [(5, 256), (1, 256)]
    assert address not in uploads and all(source != address for source, _ in downloads)
    assert [size for _, size in downloads].count(ctypes.sizeof(ctypes.c_int32)) == 1
    assert not array._storage.host_current
    assert array.get(0) == 3
    cuda.close()


@pytest.mark.parametrize("failure", ["scratch_allocation", "second_launch"])
def test_failed_reduction_releases_all_allocations(cuda, monkeypatch, failure):
    allocations = set()
    allocate, release, launch = cuda.libcuda.cuMemAlloc_v2, cuda.libcuda.cuMemFree_v2, cuda.libcuda.cuLaunchKernel
    allocation_count, launch_count = 0, 0

    def record_allocate(destination, size):
        nonlocal allocation_count
        allocation_count += 1
        # Payload, descriptor, result, then the second scratch buffer.
        if failure == "scratch_allocation" and allocation_count == 4:
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

    def fail_second_launch(*args):
        nonlocal launch_count
        launch_count += 1
        return 1 if failure == "second_launch" and launch_count == 2 else launch(*args)

    monkeypatch.setattr(cuda.libcuda, "cuMemAlloc_v2", record_allocate)
    monkeypatch.setattr(cuda.libcuda, "cuMemFree_v2", record_release)
    monkeypatch.setattr(cuda.libcuda, "cuLaunchKernel", fail_second_launch)
    array = full((513,), 7)
    ty = LLVMNDArrayType(LLVMInt, 1)
    backend = Backend(cuda, CUDALLVMIRGenerator(), CUDALLVMLowerer())
    with pytest.raises(CUDAExecutionError, match="reduction"):
        execute(backend, "fun a => NDArray_reduce a (fun acc => fun x => acc + x) 0", [array], [ty], LLVMInt)
    assert not allocations
    assert array.get(0) == 7 and array._storage.device is None


@pytest.mark.parametrize("mode", ["interpreted", "cpu", "cuda"])
def test_runnable_reduction_example(mode, request, monkeypatch, capsys):
    if mode == "cuda":
        engine = request.getfixturevalue("cuda")

        def initialize(pipeline):
            pipeline.cuda_initialized = True
            pipeline.register_backend("cuda", Backend(engine, CUDALLVMIRGenerator(), CUDALLVMLowerer()))

        monkeypatch.setattr(MultiBackendPipeline, "_initialize_cuda_backend", initialize)
    path = Path(__file__).resolve().parents[1] / "examples/llvm/gpu/reductions.ae"
    source = path.read_text()
    if mode == "interpreted":
        source = source.replace("@gpu\n", "")
    elif mode == "cpu":
        source = source.replace("@gpu\n", "@llvm\n")
    driver = AeonDriver(AeonConfig(synthesizer="none", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0))
    assert not driver.parse(aeon_code=source)
    driver.run()
    assert capsys.readouterr().out.strip().splitlines() == ["524800", "0", "1024"]
