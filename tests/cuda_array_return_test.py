"""CUDA array results must preserve the identity and extent of an input buffer."""

import ctypes
from pathlib import Path

import llvmlite.binding as llvm
import pytest

from aeon.core.parser import parse_term, parse_type
from aeon.compilation.compile import compile_and_link
from aeon.llvm.core import Backend
from aeon.llvm.cpu.converter import CPULLVMIRGenerator
from aeon.llvm.cpu.executor import CPULLVMExecutionEngine
from aeon.llvm.cuda.converter import CUDALLVMIRGenerator
from aeon.llvm.cuda.executor import CUDAExecutionEngine, CUDAExecutionError
from aeon.llvm.cuda.lowerer import CUDALLVMLowerer
from aeon.llvm.llvm_ast import (
    LLVMChar,
    LLVMFunction,
    LLVMFunctionType,
    LLVMGetElementPtr,
    LLVMInt,
    LLVMDouble,
    LLVMLong,
    LLVMLiteral,
    LLVMPointerType,
    LLVMVar,
)
from aeon.llvm.utils import to_llvm_type
from aeon.llvm.pipeline import MultiBackendPipeline
from aeon.utils.name import Name


def array_function(body, signature):
    function = CUDALLVMLowerer().lower(parse_term(body), expected_type=to_llvm_type(parse_type(signature)))
    function.name = Name("array_result", 0)
    return function


class EmulatedCUDA:
    """Execute actual generated entry wrappers with MCJIT and host allocations."""

    def __init__(self):
        self.allocations = {}
        self.param_types = []

    def cuCtxSetCurrent(self, context):
        return 0

    def cuMemAlloc_v2(self, destination, size):
        buffer = ctypes.create_string_buffer(size)
        address = ctypes.addressof(buffer)
        self.allocations[address] = buffer
        ctypes.cast(destination, ctypes.POINTER(ctypes.c_uint64))[0] = address
        return 0

    def cuMemFree_v2(self, address):
        del self.allocations[address]
        return 0

    def cuMemcpyHtoD_v2(self, destination, source, size):
        ctypes.memmove(destination, source, size)
        return 0

    cuMemcpyDtoH_v2 = cuMemcpyHtoD_v2

    def cuLaunchKernel(self, function, gx, gy, gz, bx, by, bz, shared, stream, params, extra):
        values = [ctypes.cast(address, ctypes.POINTER(ty))[0] for address, ty in zip(params, self.param_types)]
        function(*values)
        return 0

    def cuCtxSynchronize(self):
        return 0

    def load_module(self, code):
        llvm.initialize_native_target()
        llvm.initialize_native_asmprinter()
        machine = llvm.Target.from_default_triple().create_target_machine()
        module = llvm.parse_assembly(code)
        module.triple = llvm.get_default_triple()
        module.data_layout = str(machine.target_data)
        module.verify()
        engine = llvm.create_mcjit_compiler(module, machine)
        engine.finalize_object()
        return engine

    def get_function(self, module, name):
        return ctypes.CFUNCTYPE(None, *self.param_types)(module.get_function_address(name))


@pytest.fixture(scope="module")
def cuda_engine():
    try:
        return CUDAExecutionEngine()
    except CUDAExecutionError as exc:
        pytest.skip(str(exc))


@pytest.fixture(params=["emulated", "cuda"])
def executor(request):
    if request.param == "cuda":
        return request.getfixturevalue("cuda_engine")
    engine = CUDAExecutionEngine.__new__(CUDAExecutionEngine)
    engine.libcuda = EmulatedCUDA()
    engine.context = None
    engine._module_cache = {}
    engine._compile_to_ptx = lambda code: code
    engine._load_module = engine.libcuda.load_module
    engine._get_function = engine.libcuda.get_function
    return engine


def execute(executor, function, args):
    if isinstance(executor.libcuda, EmulatedCUDA):
        executor.libcuda.param_types = [
            ctypes.c_void_p if isinstance(ty, LLVMPointerType) else executor._get_ctypes_type(ty)
            for ty in function.arg_types
        ] + [ctypes.c_void_p]
    code = CUDALLVMIRGenerator().generate_ir([function])
    llvm.parse_assembly(code).verify()
    try:
        return executor.execute(code, "array_result", args, function.arg_types, function.type.return_type)
    finally:
        if isinstance(executor.libcuda, EmulatedCUDA):
            assert not executor.libcuda.allocations


@pytest.mark.parametrize("element,values", [("Int", [5, 6, 7]), ("Float", [1.5, 2.5, 3.5])])
def test_return_updated_input_array(executor, element, values):
    values = list(values)
    zero = "0.0" if element == "Float" else "0"
    function = array_function(
        f"fun xs => let ys = set xs 1 {zero} in set ys 2 {zero}", f"(xs:(Array {element})) -> (Array {element})"
    )
    original_first = values[0]
    result = execute(executor, function, [values])
    assert result is values
    assert result == [original_first, 0, 0]


@pytest.mark.parametrize("element,values", [(LLVMLong, [2**40, -(2**40)]), (LLVMDouble, [1e100, -1e100])])
def test_return_input_preserves_element_width(executor, element, values):
    values = list(values)
    expected = list(values)
    pointer = LLVMPointerType(element)
    function = LLVMFunction(
        LLVMFunctionType([pointer], pointer),
        [Name("xs", 0)],
        [pointer],
        LLVMVar(pointer, Name("xs", 0)),
        Name("array_result", 0),
    )
    assert execute(executor, function, [values]) is values
    assert values == expected


@pytest.mark.parametrize("values", [[], [1], [1, 2, 3]])
def test_return_input_uses_actual_length_not_scalar_argument(executor, values):
    function = array_function("fun xs => fun n => xs", "(xs:(Array Int)) -> (n:Int) -> (Array Int)")
    assert execute(executor, function, [values, 99]) is values


@pytest.mark.parametrize("pick_first", [True, False])
def test_return_selected_array_parameter(executor, pick_first):
    function = array_function(
        "fun xs => fun ys => fun first => if first then xs else ys",
        "(xs:(Array Int)) -> (ys:(Array Int)) -> (first:Bool) -> (Array Int)",
    )
    xs, ys = [1], [2, 3, 4]
    result = execute(executor, function, [xs, ys, pick_first])
    assert result is (xs if pick_first else ys)


def test_reject_interior_pointer_and_free_allocations(executor):
    pointer = LLVMPointerType(LLVMInt)
    function = LLVMFunction(
        LLVMFunctionType([pointer], pointer),
        [Name("xs", 0)],
        [pointer],
        LLVMGetElementPtr(pointer, LLVMVar(pointer, Name("xs", 0)), [LLVMLiteral(LLVMInt, 1)]),
        Name("array_result", 0),
    )
    with pytest.raises(CUDAExecutionError, match="does not refer to an array passed as a parameter"):
        execute(executor, function, [[1, 2]])


def test_opaque_pointer_returns_remain_device_local():
    pointer = LLVMPointerType(LLVMChar)
    function = LLVMFunction(
        LLVMFunctionType([pointer], pointer),
        [Name("xs", 0)],
        [pointer],
        LLVMVar(pointer, Name("xs", 0)),
        Name("array_result", 0),
    )
    code = CUDALLVMIRGenerator().generate_ir([function])
    llvm.parse_assembly(code).verify()
    assert "array_result__kernel" not in code
    executor = CUDAExecutionEngine.__new__(CUDAExecutionEngine)
    executor.libcuda = EmulatedCUDA()
    executor.context = None
    with pytest.raises(CUDAExecutionError, match="must refer to an array passed as a parameter"):
        executor.execute(code, "array_result", [[1]], [pointer], pointer)
    assert not executor.libcuda.allocations


def test_array_set_chain_also_returns_buffer_on_cpu():
    function = array_function("fun xs => let ys = set xs 1 0 in set ys 2 0", "(xs:(Array Int)) -> (Array Int)")
    code = CPULLVMIRGenerator().generate_ir([function])
    result = CPULLVMExecutionEngine().execute(
        code, "array_result", [[5, 6, 7]], function.arg_types, function.type.return_type
    )
    assert result == [5, 0, 0]


@pytest.fixture(scope="module")
def array_return_example():
    path = Path(__file__).resolve().parents[1] / "examples/llvm/gpu/array_return.ae"
    _, core, _, metadata, _, errors = compile_and_link(str(path), is_main=True, is_main_hole=False)
    assert not errors
    return core, metadata


@pytest.mark.parametrize("target", ["cpu", "cuda"])
def test_checked_array_return_example(array_return_example, target, request):
    core, metadata = array_return_example
    pipeline = MultiBackendPipeline(metadata)
    if target == "cuda":
        executor = request.getfixturevalue("cuda_engine")
        pipeline.register_backend("cuda", Backend(executor, CUDALLVMIRGenerator(), CUDALLVMLowerer()))
    # Prevent initialization for the CPU fallback; reuse the fixture on CUDA.
    pipeline.cuda_initialized = True
    pipeline.compile(core)
    name = next(name for name in pipeline.function_targets if name.name == "zero_first")
    assert pipeline.function_targets[name] == target
    values = [7, 8, 9]
    result = pipeline.invoke(name, [values])
    assert result == [0, 8, 9]
    if target == "cuda":
        assert result is values


@pytest.mark.parametrize("target", ["cpu", "cuda"])
def test_checked_zero_matrix_example(target, request):
    path = Path(__file__).resolve().parents[1] / "examples/llvm/gpu/zero_matrix.ae"
    _, core, _, metadata, _, errors = compile_and_link(str(path), is_main=True, is_main_hole=False)
    assert not errors
    pipeline = MultiBackendPipeline(metadata)
    if target == "cuda":
        executor = request.getfixturevalue("cuda_engine")
        pipeline.register_backend("cuda", Backend(executor, CUDALLVMIRGenerator(), CUDALLVMLowerer()))
    pipeline.cuda_initialized = True
    pipeline.compile(core)
    name = next(name for name in pipeline.function_targets if name.name == "zero_matrix")
    assert pipeline.function_targets[name] == target
    for values in ([], [7], [1, -2, 3, 4], list(range(32))):
        result = pipeline.invoke(name, [values, len(values)])
        assert result == [0] * len(values)
        if target == "cuda":
            assert result is values
