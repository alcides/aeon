"""Owned reshapes, rank/shape contracts, and shared CPU/CUDA NDArray lowering."""

import ctypes
import math
from pathlib import Path

import llvmlite.binding as llvm
import pytest

from aeon.bindings.ndarray import NDArray, full, from_array
from aeon.bindings.floyd_warshall import prepare_graph, check_negative_cycles
from aeon.compilation.compile import compile_and_link
from aeon.core.parser import parse_term
from aeon.facade.api import LinearityError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.llvm.core import Backend, LLVMValidationError
from aeon.llvm.cpu.converter import CPULLVMIRGenerator
from aeon.llvm.cpu.executor import CPULLVMExecutionEngine
from aeon.llvm.cpu.lowerer import CPULLVMLowerer
from aeon.llvm.cuda.converter import CUDALLVMIRGenerator
from aeon.llvm.cuda.executor import CUDAExecutionEngine, CUDAExecutionError
from aeon.llvm.cuda.lowerer import CUDALLVMLowerer
from aeon.llvm.llvm_ast import (
    LLVMInt,
    LLVMFloat,
    LLVMDouble,
    LLVMLong,
    LLVMBool,
    LLVMNDArrayType,
    LLVMFunctionType,
)
from aeon.llvm.ndarray import NDArrayDescriptor
from aeon.llvm.pipeline import MultiBackendPipeline
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.name import Name


def source_errors(source):
    driver = AeonDriver(AeonConfig(synthesizer="none", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0))
    return list(driver.parse(aeon_code=source))


@pytest.fixture(scope="module")
def cuda():
    try:
        return CUDAExecutionEngine()
    except CUDAExecutionError as exc:
        pytest.skip(str(exc))


@pytest.fixture(params=["cpu", "cuda"])
def backend(request):
    if request.param == "cuda":
        return Backend(request.getfixturevalue("cuda"), CUDALLVMIRGenerator(), CUDALLVMLowerer())
    return Backend(CPULLVMExecutionEngine(), CPULLVMIRGenerator(), CPULLVMLowerer())


def execute(backend, body, arguments, types, result_type):
    backend.generator = type(backend.generator)()
    function = backend.lowerer.lower(parse_term(body), expected_type=LLVMFunctionType(types, result_type))
    function.name = Name("nd_test", 0)
    code = backend.generator.generate_ir([function])
    llvm.parse_assembly(code).verify()
    launch = getattr(backend.generator, "ndarray_launches", {}).get("nd_test")
    shape = arguments[launch[0]].shape if launch else None
    row_index = getattr(backend.generator, "row_launches", {}).get("nd_test")
    if row_index is not None:
        shape = (arguments[row_index].shape[0],)
    return backend.executor.execute(code, "nd_test", arguments, types, result_type, launch_shape=shape)


@pytest.mark.parametrize("shape", [(6,), (2, 3), (1, 2, 3), (0, 3), (2, 0, 4)])
def test_owned_flatten_and_reshape_round_trip(shape):
    array = full(shape, 7)
    data = array.data
    flat = array.to_1d()
    assert flat.data is data
    assert flat.shape == (len(data),)
    with pytest.raises(ValueError, match="ownership"):
        _ = array.data
    result = flat.reshape(shape)
    assert result.data is data
    assert result.shape == shape
    with pytest.raises(ValueError, match="ownership"):
        _ = flat.shape


def test_array_bridge_transfers_original_list():
    values = [1, 2, 3, 4]
    array = from_array(values)
    matrix = array.from_1d2(2, 2)
    result = matrix.to_1d().to_array()
    assert result is values
    assert result == [1, 2, 3, 4]


@pytest.mark.parametrize("shape", [(), (1, 2, 3, 4), (-1, 2), (True, 2), (2**31,), (2**30, 4)])
def test_invalid_dimensions(shape):
    with pytest.raises(ValueError):
        full(shape, 0)


def test_invalid_reshape_does_not_consume_owner():
    array = NDArray([1, 2, 3], (3,))
    with pytest.raises(ValueError, match="element count"):
        array.from_1d2(2, 2)
    assert array.data == [1, 2, 3]
    assert array.shape == (3,)


@pytest.mark.parametrize("indices", [(-1, 0), (0, -1), (2, 0), (0, 3), (0,), (0, 0, 0)])
def test_runtime_index_bounds(indices):
    array = full((2, 3), 7)
    with pytest.raises(IndexError):
        array.get(*indices)


@pytest.mark.parametrize("shape", [(0,), (33,), (0, 5), (17, 33), (5, 0, 17), (5, 9, 17)])
def test_parallel_fill_returns_input_descriptor(backend, shape):
    array = full(shape, 7)
    ty = LLVMNDArrayType(LLVMInt, len(shape))
    result = execute(backend, "fun m => NDArray_fill m 0", [array], [ty], ty)
    assert result is array
    assert result.shape == shape
    assert result.data == [0] * result.elements
    if isinstance(backend.generator, CUDALLVMIRGenerator):
        assert backend.generator.ndarray_launches["nd_test"] == (0, len(shape))


@pytest.mark.parametrize("element,value", [(LLVMFloat, 1.5), (LLVMDouble, 1e100), (LLVMLong, 2**40), (LLVMBool, True)])
def test_fill_preserves_element_type_and_scalar_argument(backend, element, value):
    array = full((17, 33), 0)
    ty = LLVMNDArrayType(element, 2)
    result = execute(backend, "fun m => fun v => NDArray_fill m v", [array, value], [ty, element], ty)
    assert result is array
    assert result.data == [value] * array.elements


@pytest.mark.parametrize("shape,indices", [((2, 3), (1, 2)), ((2, 3, 4), (1, 2, 3))])
def test_compiled_multidimensional_indexing(backend, shape, indices):
    array = full(shape, 7)
    ty = LLVMNDArrayType(LLVMInt, len(shape))
    index_args = " ".join(str(i) for i in indices)
    result = execute(backend, f"fun m => NDArray_set{len(shape)} m {index_args} 42", [array], [ty], ty)
    assert result is array
    assert result.data[:-1] == [7] * (array.elements - 1)
    assert execute(backend, f"fun m => NDArray_get{len(shape)} m {index_args}", [array], [ty], LLVMInt) == 42


@pytest.mark.parametrize("column", [-1, 3])
def test_compiled_index_bounds(backend, column):
    array = full((2, 3), 7)
    ty = LLVMNDArrayType(LLVMInt, 2)
    with pytest.raises(IndexError, match="out of bounds"):
        execute(backend, f"fun m => NDArray_get2 m 0 ({column})", [array], [ty], LLVMInt)
    assert array.data == [7] * 6


@pytest.mark.parametrize("shape", [(2, 3), (1, 2, 3), (0, 7), (2, 0, 3)])
def test_compiled_1d_round_trip_without_storage_copy(backend, shape):
    array = full(shape, 7)
    data = array.data
    ty = LLVMNDArrayType(LLVMInt, len(shape))
    flat_type = LLVMNDArrayType(LLVMInt, 1)
    flat = execute(backend, "fun m => NDArray_to_1d m", [array], [ty], flat_type)
    assert flat.data is data
    assert flat.shape == (len(data),)
    with pytest.raises(ValueError, match="ownership"):
        _ = array.shape
    dimensions = " ".join(str(n) for n in shape)
    result = execute(backend, f"fun m => NDArray_from_1d{len(shape)} m {dimensions}", [flat], [flat_type], ty)
    assert result.data is data
    assert result.shape == shape
    assert result.data == [7] * len(data)


@pytest.mark.parametrize("dimensions", ["2 2", "0 3"])
def test_compiled_rejects_incompatible_reshape(backend, dimensions):
    array = NDArray([1, 2, 3], (3,))
    one = LLVMNDArrayType(LLVMInt, 1)
    two = LLVMNDArrayType(LLVMInt, 2)
    with pytest.raises(ValueError, match="reshape"):
        execute(backend, f"fun m => NDArray_from_1d2 m {dimensions}", [array], [one], two)
    assert array.shape == (3,)


def test_compiled_reshape_overflow_is_checked(backend):
    array = NDArray([], (0,))
    one, three = LLVMNDArrayType(LLVMInt, 1), LLVMNDArrayType(LLVMInt, 3)
    with pytest.raises(ValueError, match="reshape"):
        execute(backend, "fun m => NDArray_from_1d3 m 1073741824 1073741824 16", [array], [one], three)
    assert array.shape == (0,)


@pytest.mark.parametrize("axis", [0, 1, 2])
def test_compiled_dimension_witness(backend, axis):
    array = full((2, 3, 4), 7)
    ty = LLVMNDArrayType(LLVMInt, 3)
    assert execute(backend, f"fun m => NDArray_dimension m {axis}", [array], [ty], LLVMInt) == array.shape[axis]


def test_compiled_reshape_and_fill_in_one_call(backend):
    array = NDArray([1, 2, 3, 4, 5, 6], (2, 3))
    data = array.data
    two, three = LLVMNDArrayType(LLVMInt, 2), LLVMNDArrayType(LLVMInt, 3)
    result = execute(
        backend,
        "fun m => let flat = NDArray_to_1d m in let volume = NDArray_from_1d3 flat 1 2 3 in NDArray_fill volume 0",
        [array],
        [two],
        three,
    )
    assert result.shape == (1, 2, 3)
    assert result.data is data
    assert data == [0] * 6


def test_marshaling_rejects_storage_shape_mismatch(backend):
    array = full((2, 3), 7)
    array.data.pop()
    ty = LLVMNDArrayType(LLVMInt, 2)
    with pytest.raises(ValueError, match="element count"):
        execute(backend, "fun m => NDArray_get2 m 0 0", [array], [ty], LLVMInt)


def test_cuda_descriptor_error_frees_data_and_descriptor():
    from tests.cuda_array_return_test import EmulatedCUDA

    executor = CUDAExecutionEngine.__new__(CUDAExecutionEngine)
    executor.libcuda = EmulatedCUDA()
    executor.libcuda.param_types = [ctypes.c_void_p, ctypes.c_void_p]
    executor.context = None
    executor._module_cache = {}
    executor._compile_to_ptx = lambda code: code
    executor._load_module = executor.libcuda.load_module
    executor._get_function = executor.libcuda.get_function
    backend = Backend(executor, CUDALLVMIRGenerator(), CUDALLVMLowerer())
    ty = LLVMNDArrayType(LLVMInt, 2)
    with pytest.raises(IndexError):
        execute(backend, "fun m => NDArray_get2 m 0 3", [full((2, 3), 7)], [ty], LLVMInt)
    assert not executor.libcuda.allocations


def test_descriptor_abi_matches_llvm():
    ty = LLVMNDArrayType(LLVMInt, 2).to_ir().pointee
    llvm.initialize_native_target()
    data = llvm.Target.from_default_triple().create_target_machine().target_data
    assert ty.get_abi_size(data) == ctypes.sizeof(NDArrayDescriptor)
    assert [
        NDArrayDescriptor.data.offset,
        NDArrayDescriptor.offset.offset,
        NDArrayDescriptor.rank.offset,
        NDArrayDescriptor.shape.offset,
        NDArrayDescriptor.strides.offset,
        NDArrayDescriptor.error.offset,
    ] == [0, 8, 16, 24, 48, 72]


@pytest.mark.parametrize(
    "body",
    [
        "let 1 m := full2 2 3 7 in get2 m 2 0",
        "let 1 m := full2 2 3 7 in get3 m 0 0 0",
        "let 1 m := full1 6 7 in let 1 bad := from_1d2 m 2 4 in count bad",
        "let 1 m := full1 6 7 in let 1 bad := from_1d3 m 2 2 2 in count bad",
    ],
)
def test_static_shape_or_rank_errors(body):
    errors = source_errors(f"open NDArray\ndef main (args:Int) : Int := {body};")
    assert errors


def test_reshape_source_cannot_reuse_consumed_owner():
    errors = source_errors("""open NDArray
def main (args:Int) : Int :=
 let 1 m := full2 2 3 7 in
 let 1 flat := to_1d m in
 let a := count m in a + count flat;
""")
    assert any(isinstance(error, LinearityError) for error in errors)


@pytest.fixture(scope="module", params=["zero_matrix_2d.ae", "zero_volume_3d.ae"])
def checked_kernel(request):
    path = Path(__file__).resolve().parents[1] / "examples/llvm/gpu" / request.param
    _, core, _, metadata, _, errors = compile_and_link(str(path), is_main=True, is_main_hole=False)
    assert not errors
    return core, metadata, request.param


def test_checked_gpu_examples_and_cpu_fallback(backend, checked_kernel):
    core, metadata, filename = checked_kernel
    pipeline = MultiBackendPipeline(metadata)
    cuda_backend = isinstance(backend.executor, CUDAExecutionEngine)
    if cuda_backend:
        pipeline.register_backend("cuda", backend)
    else:
        pipeline.register_backend("cpu", backend)
    pipeline.cuda_initialized = True
    pipeline.compile(core)
    name = next(name for name in pipeline.function_targets if name.name.startswith("zero_"))
    assert pipeline.function_targets[name] == ("cuda" if cuda_backend else "cpu")
    shape = (17, 33) if filename == "zero_matrix_2d.ae" else (5, 9, 17)
    array = full(shape, 7)
    result = pipeline.invoke(name, [array])
    assert result is array
    assert result.shape == shape
    assert result.data == [0] * array.elements


def test_reshape_methods_example_runs(capsys):
    path = Path(__file__).resolve().parents[1] / "examples/llvm/ndarray_reshape.ae"
    driver = AeonDriver(AeonConfig(synthesizer="none", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0))
    assert not driver.parse(aeon_code=path.read_text())
    driver.run()
    assert capsys.readouterr().out.strip() == "6"


@pytest.fixture(scope="module")
def checked_nbody():
    path = Path(__file__).resolve().parents[1] / "examples/llvm/gpu/nbody.ae"
    _, core, _, metadata, _, errors = compile_and_link(str(path), is_main=True, is_main_hole=False)
    assert not errors
    return core, metadata


def nbody_reference(state, dt, softening):
    """Independent, double-precision all-pairs reference with G = 1."""
    result = []
    for body in state:
        acceleration = [0.0, 0.0, 0.0]
        for other in state:
            delta = [other[k] - body[k] for k in range(3)]
            distance = math.sqrt(sum(d * d for d in delta) + softening**2)
            for k in range(3):
                acceleration[k] += other[6] * delta[k] / distance**3
        velocity = [body[3 + k] + dt * acceleration[k] for k in range(3)]
        position = [body[k] + dt * velocity[k] for k in range(3)]
        result.append(position + velocity + [body[6]])
    return result


@pytest.mark.parametrize("steps", [1, 5])
@pytest.mark.parametrize(
    "state",
    [
        [],
        [[1.0, 2.0, 3.0, 0.125, -0.25, 0.5, 2.0]],
        [[-1.0, 0.0, 0.0, 0.0, -0.5, 0.0, 1.0], [1.0, 0.0, 0.0, 0.0, 0.5, 0.0, 1.0]],
        [[-1.0, 0.0, 0.0, 0.0, -0.5, 0.0, 3.0], [1.0, 0.0, 0.0, 0.0, 0.5, 0.0, 1.0]],
        [[0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1.0], [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2.0]],
        [
            [-1.0, 0.5, 0.25, 0.125, -0.25, 0.5, 1.0],
            [1.0, -0.5, 0.125, 0.25, 0.125, -0.25, 2.0],
            [0.5, 1.0, -0.25, -0.125, 0.5, 0.25, 0.5],
            [-0.5, -1.0, 0.5, -0.25, -0.125, -0.5, 1.5],
        ],
        [
            [
                (i % 17 - 8) * 0.25,
                (i // 17 - 8) * 0.25,
                (i % 5) * 0.125,
                (i % 3 - 1) * 0.03125,
                (i % 7 - 3) * 0.015625,
                0.0625,
                0.125 + (i % 3) * 0.0625,
            ]
            for i in range(257)
        ],
    ],
    ids=["empty", "ballistic", "equal-masses", "unequal-masses", "coincident", "four-bodies-3d", "257-bodies"],
)
def test_nbody_gpu_example_against_reference(backend, checked_nbody, state, steps, monkeypatch):
    core, metadata = checked_nbody
    pipeline = MultiBackendPipeline(metadata)
    target = "cuda" if isinstance(backend.executor, CUDAExecutionEngine) else "cpu"
    pipeline.register_backend(target, backend)
    pipeline.cuda_initialized = True
    pipeline.compile(core)
    name = pipeline.name_to_id_cache["nbody_step"]
    assert pipeline.function_targets[name] == target
    launches = []
    if target == "cuda":
        assert "llvm.sqrt.f64" in pipeline.llvm_ir_by_backend[target]
        from aeon.llvm.utils import sanitize_name

        compiled_name = sanitize_name(name)
        assert backend.generator.row_launches[compiled_name] == 4
        kernel_ir = str(backend.generator.module.globals[compiled_name + "__kernel"])
        assert "llvm.nvvm.read.ptx.sreg.tid.x" in kernel_ir
        assert "llvm.nvvm.read.ptx.sreg.ctaid.x" in kernel_ir
        launch = backend.executor.libcuda.cuLaunchKernel

        def record_launch(function, gx, gy, gz, bx, by, bz, *args):
            launches.append(((gx, gy, gz), (bx, by, bz)))
            return launch(function, gx, gy, gz, bx, by, bz, *args)

        monkeypatch.setattr(backend.executor.libcuda, "cuLaunchKernel", record_launch)

    actual = [list(body) for body in state]
    expected = [list(body) for body in state]
    n, dt, softening = len(state), 0.01, 0.05
    for _ in range(steps):
        snapshot = [value for body in actual for value in body]
        source_before = list(snapshot)
        output = full((n, 7), float("nan"))
        result = pipeline.invoke(name, [snapshot, n, dt, softening, output])
        assert result is output
        assert result.shape == (n, 7)
        assert snapshot == source_before
        assert all(math.isfinite(value) for value in result.data)
        actual = [result.data[i * 7 : (i + 1) * 7] for i in range(n)]
        expected = nbody_reference(expected, dt, softening)
        assert result.data == pytest.approx([value for body in expected for value in body], rel=2e-5, abs=2e-6)
        assert [body[6] for body in actual] == [body[6] for body in state]
    if target == "cuda":
        expected_grid = (max(1, (n + 255) // 256), 1, 1)
        assert launches == [(expected_grid, (256, 1, 1))] * steps


def test_nbody_main_runs(capsys):
    path = Path(__file__).resolve().parents[1] / "examples/llvm/gpu/nbody.ae"
    driver = AeonDriver(AeonConfig(synthesizer="none", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0))
    assert not driver.parse(aeon_code=path.read_text())
    driver.run()
    expected = [
        [
            (i % 17 - 8) * 0.25,
            (i // 17 - 8) * 0.25,
            (i % 5) * 0.125,
            (i % 3 - 1) * 0.03125,
            (i % 7 - 3) * 0.015625,
            0.0625,
            0.125 + (i % 3) * 0.0625,
        ]
        for i in range(257)
    ]
    for _ in range(10):
        expected = nbody_reference(expected, 0.01, 0.05)
    assert float(capsys.readouterr().out.strip()) == pytest.approx(expected[0][0], abs=2e-6)


@pytest.mark.parametrize("shape", [(0, 7), (5, 0), (1, 3), (256, 1), (257, 7), (513, 3)])
def test_map_rows_disjoint_updates_and_captured_scalar(backend, shape):
    array = full(shape, -1)
    ty = LLVMNDArrayType(LLVMInt, 2)
    result = execute(
        backend,
        "fun m => fun salt => NDArray_map_rows m (fun i => fun row => NDArray_fill row (i + salt))",
        [array, 11],
        [ty, LLVMInt],
        ty,
    )
    assert result is array
    assert result.shape == shape
    assert result.data == [i + 11 for i in range(shape[0]) for _ in range(shape[1])]
    if isinstance(backend.executor, CUDAExecutionEngine):
        assert backend.generator.row_launches["nd_test"] == 0


@pytest.mark.parametrize("element,value", [(LLVMFloat, 1.25), (LLVMDouble, 1e100), (LLVMBool, True)])
def test_map_rows_preserves_scalar_element_type(backend, element, value):
    array = full((257, 3), 0)
    ty = LLVMNDArrayType(element, 2)
    result = execute(
        backend,
        "fun m => fun v => NDArray_map_rows m (fun i => fun row => NDArray_fill row v)",
        [array, value],
        [ty, element],
        ty,
    )
    assert result is array
    assert result.data == [value] * array.elements


@pytest.mark.parametrize("column", [-1, 3])
def test_map_rows_propagates_parallel_row_errors(backend, column):
    array = full((257, 3), 7)
    ty = LLVMNDArrayType(LLVMInt, 2)
    with pytest.raises(IndexError, match="out of bounds"):
        execute(
            backend,
            "fun m => fun col => NDArray_map_rows m (fun i => fun row => NDArray_set1 row col i)",
            [array, column],
            [ty, LLVMInt],
            ty,
        )


def test_map_rows_rejects_capturing_owned_array(backend):
    matrix = full((3, 2), 0)
    captured = full((2,), 7)
    matrix_type, row_type = LLVMNDArrayType(LLVMInt, 2), LLVMNDArrayType(LLVMInt, 1)
    with pytest.raises(LLVMValidationError, match="cannot capture owned"):
        execute(
            backend,
            "fun m => fun other => NDArray_map_rows m (fun i => fun row => NDArray_fill other i)",
            [matrix, captured],
            [matrix_type, row_type],
            matrix_type,
        )


def test_interpreted_map_rows_preserves_matrix_and_consumes_rows():
    array = full((3, 2), 0)
    rows = []

    def callback(index):
        def update(row):
            rows.append(row)
            return row.fill(index + 1)

        return update

    assert array.map_rows(callback) is array
    assert array.data == [1, 1, 2, 2, 3, 3]
    for row in rows:
        with pytest.raises(ValueError, match="ownership"):
            _ = row.data


def test_interpreted_map_rows_rejects_changed_row_shape():
    array = full((2, 3), 7)
    with pytest.raises(ValueError, match="preserve the row shape"):
        array.map_rows(lambda index: lambda row: row.from_1d2(1, 3))
    assert array.shape == (2, 3)
    assert array.data == [7] * 6


@pytest.fixture(scope="module")
def checked_floyd():
    path = Path(__file__).resolve().parents[1] / "examples/llvm/gpu/floyd_warshall.ae"
    _, core, _, metadata, _, errors = compile_and_link(str(path), is_main=True, is_main_hole=False)
    assert not errors
    return core, metadata


def shortest_paths_reference(graph):
    """Bellman–Ford from every source, independent of the GPU pivot algorithm."""
    n = len(graph)
    edges = [(i, j, weight) for i, row in enumerate(graph) for j, weight in enumerate(row) if math.isfinite(weight)]
    result = []
    for source in range(n):
        distances = [math.inf] * n
        distances[source] = 0.0
        for _ in range(n - 1):
            changed = False
            for i, j, weight in edges:
                candidate = distances[i] + weight
                if candidate < distances[j]:
                    distances[j] = candidate
                    changed = True
            if not changed:
                break
        if any(distances[i] + weight < distances[j] for i, j, weight in edges):
            raise ValueError("negative-weight cycle")
        result.append(distances)
    return result


@pytest.mark.parametrize(
    "graph",
    [
        [],
        [[math.inf]],
        [
            [0.0, 5.0, math.inf, 10.0],
            [math.inf, 0.0, 3.0, math.inf],
            [math.inf, math.inf, 0.0, 1.0],
            [math.inf, math.inf, math.inf, 0.0],
        ],
        [[0.0, math.inf, math.inf], [math.inf, 0.0, -5.0], [math.inf, math.inf, 0.0]],
        [[3.0, -2.0, 5.0], [math.inf, 4.0, 3.0], [math.inf, math.inf, 5.0]],
        [[0.0, 2.0, math.inf], [2.0, 0.0, 1.0], [math.inf, 1.0, 0.0]],
        [[0.0, 0.5, 2.0], [math.inf, 0.0, -0.25], [math.inf, math.inf, 0.0]],
        [[0.0, -2.0, math.inf], [math.inf, 0.0, 3.0], [1.0, math.inf, 0.0]],
        [
            [0.0 if i == j else float((i * 7 + j * 3) % 11 - 4) if i < j else math.inf for j in range(7)]
            for i in range(7)
        ],
    ],
    ids=[
        "empty",
        "singleton",
        "indirect-path",
        "unreachable-negative-edge",
        "positive-self-loops",
        "undirected",
        "fractional",
        "negative-edge-positive-cycle",
        "dense-dag",
    ],
)
def test_floyd_warshall_gpu_against_bellman_ford(backend, checked_floyd, graph, monkeypatch):
    core, metadata = checked_floyd
    pipeline = MultiBackendPipeline(metadata)
    target = "cuda" if isinstance(backend.executor, CUDAExecutionEngine) else "cpu"
    pipeline.register_backend(target, backend)
    pipeline.cuda_initialized = True
    pipeline.compile(core)
    name = pipeline.name_to_id_cache["floyd_pass"]
    assert pipeline.function_targets[name] == target
    launches = []
    if target == "cuda":
        from aeon.llvm.utils import sanitize_name

        compiled_name = sanitize_name(name)
        assert backend.generator.row_launches[compiled_name] == 3
        launch = backend.executor.libcuda.cuLaunchKernel

        def record_launch(function, gx, gy, gz, bx, by, bz, *args):
            launches.append(((gx, gy, gz), (bx, by, bz)))
            return launch(function, gx, gy, gz, bx, by, bz, *args)

        monkeypatch.setattr(backend.executor.libcuda, "cuLaunchKernel", record_launch)

    n = len(graph)
    distances = prepare_graph(NDArray([weight for row in graph for weight in row], (n, n)))
    for k in range(n):
        previous = list(distances.data)
        output = full((n, n), float("nan"))
        result = pipeline.invoke(name, [previous, n, k, output])
        assert result is output
        assert result.shape == (n, n)
        assert previous == distances.data
        assert not any(math.isnan(value) for value in result.data)
        distances = result
    assert check_negative_cycles(distances) is distances
    expected = shortest_paths_reference(graph)
    assert distances.data == [weight for row in expected for weight in row]
    if target == "cuda":
        assert launches == [((1, 1, 1), (256, 1, 1))] * n


def test_floyd_warshall_main_runs(capsys):
    path = Path(__file__).resolve().parents[1] / "examples/llvm/gpu/floyd_warshall.ae"
    driver = AeonDriver(AeonConfig(synthesizer="none", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0))
    assert not driver.parse(aeon_code=path.read_text())
    driver.run()
    assert float(capsys.readouterr().out.strip()) == 9.0


def test_floyd_pivot_across_multiple_blocks(backend, checked_floyd):
    core, metadata = checked_floyd
    pipeline = MultiBackendPipeline(metadata)
    target = "cuda" if isinstance(backend.executor, CUDAExecutionEngine) else "cpu"
    pipeline.register_backend(target, backend)
    pipeline.cuda_initialized = True
    pipeline.compile(core)
    name = pipeline.name_to_id_cache["floyd_pass"]
    assert pipeline.function_targets[name] == target
    n, pivot = 257, 128
    graph = [[math.inf] * n for _ in range(n)]
    for i in range(n):
        graph[i][i] = 0.0
        if i != pivot:
            graph[i][pivot] = float(1 + i % 5)
            graph[pivot][i] = float(2 + i % 7)
    snapshot = [weight for row in graph for weight in row]
    output = full((n, n), float("nan"))
    result = pipeline.invoke(name, [snapshot, n, pivot, output])
    assert result is output
    assert result.shape == (n, n)
    assert snapshot == [weight for row in graph for weight in row]
    expected = shortest_paths_reference(graph)
    assert result.data == [weight for row in expected for weight in row]


@pytest.mark.parametrize(
    "graph",
    [[[-1.0]], [[0.0, -2.0], [1.0, 0.0]], [[0.0, math.inf, math.inf], [math.inf, 0.0, -3.0], [math.inf, 1.0, 0.0]]],
)
def test_floyd_warshall_rejects_negative_cycles(graph):
    path = Path(__file__).resolve().parents[1] / "examples/llvm/gpu/floyd_warshall.ae"
    prefix = path.read_text().rsplit("def main", 1)[0]
    n = len(graph)
    entries = ", ".join("float('inf')" if weight == math.inf else repr(weight) for row in graph for weight in row)
    source = (
        prefix
        + f"""
def main (args:Int) : Unit :=
    let 1 graph : {{m:(NDArray Float Rank2) | m.dimension_size 0 = {n} && m.dimension_size 1 = {n} && m.elements = {n * n}}} :=
        native "__import__('aeon.bindings.ndarray', fromlist=['NDArray']).NDArray([{entries}], ({n}, {n}))" in
    let 1 result := floyd_warshall {n} graph in
    result.discard;
"""
    )
    driver = AeonDriver(AeonConfig(synthesizer="none", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0))
    assert not driver.parse(aeon_code=source)
    with pytest.raises(ValueError, match="negative-weight cycle"):
        driver.run()
    with pytest.raises(ValueError, match="negative-weight cycle"):
        shortest_paths_reference(graph)


@pytest.mark.parametrize("weight", [float("nan"), -math.inf])
def test_floyd_graph_rejects_invalid_weights(weight):
    with pytest.raises(ValueError, match="finite or positive infinity"):
        prepare_graph(NDArray([weight], (1, 1)))


def test_floyd_graph_rejects_non_square_matrix():
    with pytest.raises(ValueError, match="square"):
        prepare_graph(full((2, 3), 0.0))
