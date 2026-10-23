"""Array plans execute on real CPU/CUDA backends, with observable launch/copy contracts."""

import math
from pathlib import Path

import llvmlite.binding as llvm
import pytest

from aeon.bindings.ndarray import NDArray, ManagedArray, full
from aeon.core.parser import parse_term
from aeon.llvm.array_plan import build_plans
from aeon.llvm.cuda.array_runtime import execute_array
from aeon.llvm.cuda.executor import CUDAExecutionEngine, CUDAExecutionError
from aeon.llvm.llvm_ast import LLVMFunctionType, LLVMNDArrayType, LLVMInt, LLVMFloat, LLVMDouble, LLVMLong, LLVMBool
from aeon.llvm.pipeline import MultiBackendPipeline
from aeon.utils.name import Name
from tests.cuda_reduction_test import backend as backend, cuda as cuda


def compile_plan(backend, body, types, result, helpers=()):
    backend.generator = type(backend.generator)()
    node = backend.lowerer.lower(
        parse_term(body),
        expected_type=LLVMFunctionType(types, result),
        type_env={h.name: h.type for h in helpers},
        env={h.name: h for h in helpers},
    )
    node.name = Name("pipeline_test", 0)
    definitions, plans = build_plans([*helpers, node])
    code = backend.generator.generate_ir(definitions)
    llvm.parse_assembly(code).verify()
    pipeline = MultiBackendPipeline()
    target = "cuda" if isinstance(backend.executor, CUDAExecutionEngine) else "cpu"
    pipeline.backends[target] = backend
    pipeline.llvm_ir_by_backend[target] = code

    def invoke(function, arguments, operation, destination):
        if operation is not None and target == "cuda":
            return execute_array(backend.executor, code, function, arguments, operation)
        return pipeline._invoke_compiled(
            target, function.name, arguments, function.arg_types, function.type.return_type
        )

    plan = plans.get(node.name)
    return (
        lambda *args: plan.run(args, invoke) if plan is not None else invoke(node, list(args), None, None),
        code,
        plan,
    )


@pytest.mark.parametrize("shape", [(0,), (1,), (257,), (2, 17), (2, 3, 5)])
def test_map_zip_fusion_preserves_shape(backend, shape):
    ty = LLVMNDArrayType(LLVMInt, len(shape))
    run, code, plan = compile_plan(
        backend,
        "fun a => fun b => fun bias => let c = NDArray_zipWith a b (fun x => fun y => x + y) in "
        "let d = NDArray_map c (fun x => x * 2) in NDArray_map d (fun x => x + bias)",
        [ty, ty, LLVMInt],
        ty,
    )
    n = math.prod(shape)
    a, b = NDArray(list(range(n)), shape), full(shape, 3)
    result = run(a, b, 7)
    assert result.shape == shape
    assert result.data == [2 * (i + 3) + 7 for i in range(n)]
    assert len(plan.steps) == 1
    assert "cudaLaunchDevice" not in code


@pytest.mark.parametrize(
    "element,values,expected",
    [
        (LLVMFloat, [1.25, 2.5], [2.5, 5]),
        (LLVMDouble, [1.25, 2.5], [2.5, 5]),
        (LLVMLong, [2**35, -(2**35)], [2**36, -(2**36)]),
    ],
)
def test_map_element_types(backend, element, values, expected):
    ty = LLVMNDArrayType(element, 1)
    run, _, _ = compile_plan(backend, "fun a => NDArray_map a (fun x => x + x)", [ty], ty)
    assert run(NDArray(values.copy(), (2,))).data == expected


def test_map_can_change_element_type(backend):
    ty, result = LLVMNDArrayType(LLVMInt, 2), LLVMNDArrayType(LLVMBool, 2)
    run, _, _ = compile_plan(backend, "fun a => NDArray_map a (fun x => x > 2)", [ty], result)
    a = NDArray(list(range(6)), (2, 3))
    output = run(a)
    assert output.data == [False, False, False, True, True, True]
    assert output.shape == (2, 3)


@pytest.mark.parametrize("exclusive", [False, True])
@pytest.mark.parametrize("size", [0, 1, 17, 255, 256, 257, 65537])
def test_hierarchical_scan(backend, exclusive, size):
    ty = LLVMNDArrayType(LLVMInt, 1)
    op = "scan_exclusive" if exclusive else "scan"
    run, _, _ = compile_plan(backend, f"fun a => NDArray_{op} a (fun x => fun y => x + y) 19", [ty], ty)
    values = [i % 7 - 3 for i in range(size)]
    expected, acc = [], 19
    for value in values:
        if exclusive:
            expected.append(acc)
        acc += value
        if not exclusive:
            expected.append(acc)
    assert run(NDArray(values, (size,))).data == expected


@pytest.mark.parametrize(
    "callback,expected", [("fun x => fun y => x", [19] * 1025), ("fun x => fun y => y", list(range(1025)))]
)
def test_scan_preserves_noncommutative_order_and_applies_seed_once(backend, callback, expected):
    ty = LLVMNDArrayType(LLVMInt, 1)
    run, _, _ = compile_plan(backend, f"fun a => NDArray_scan a ({callback}) 19", [ty], ty)
    assert run(NDArray(list(range(1025)), (1025,))).data == expected


@pytest.mark.parametrize(
    "shape,axis",
    [
        ((513,), 0),
        ((3, 513), 1),
        ((513, 3), 0),
        ((2, 3, 5), 0),
        ((2, 3, 5), 1),
        ((2, 3, 5), 2),
        ((0, 3), 0),
        ((0, 3), 1),
        ((2, 0, 3), 1),
    ],
)
def test_axis_reductions(backend, shape, axis):
    ty = LLVMNDArrayType(LLVMInt, len(shape))
    run, _, _ = compile_plan(
        backend, "fun a => fun axis => NDArray_reduce_axis a axis (fun x => fun y => x + y) 11", [ty, LLVMInt], ty
    )
    values = [i % 17 - 8 for i in range(math.prod(shape))]
    reference = NDArray(values.copy(), shape).reduce_axis(axis, lambda x: lambda y: x + y, 11)
    output = run(NDArray(values, shape), axis)
    assert output.shape == reference.shape
    assert output.data == reference.data


def test_composition_keeps_filter_and_reduce_parallel(backend):
    ty = LLVMNDArrayType(LLVMInt, 2)
    run, _, plan = compile_plan(
        backend,
        "fun a => let mapped = NDArray_map a (fun x => x * 2) in "
        "let selected = NDArray_filter mapped (fun x => x % 3 == 0) in "
        "NDArray_reduce selected (fun x => fun y => x + y) 5",
        [ty],
        LLVMInt,
    )
    values = list(range(1026))
    assert run(NDArray(values.copy(), (3, 342))) == 5 + sum(2 * x for x in values if x % 3 == 0)
    if isinstance(backend.executor, CUDAExecutionEngine):
        assert backend.generator.filter_launches
        assert backend.generator.reduction_launches
    assert len(plan.steps) == 3


def test_composition_through_helper_and_branch(backend):
    ty = LLVMNDArrayType(LLVMInt, 1)
    helper = backend.lowerer.lower(
        parse_term("fun a => NDArray_map a (fun x => x + 3)"), expected_type=LLVMFunctionType([ty], ty)
    )
    helper.name = Name("map_helper", 0)
    run, _, _ = compile_plan(
        backend,
        "fun a => fun positive => if positive then map_helper a else NDArray_map a (fun x => x - 3)",
        [ty, LLVMBool],
        ty,
        [helper],
    )
    assert run(full((257,), 4), True).data == [7] * 257
    assert run(full((257,), 4), False).data == [1] * 257


def test_invalid_shapes_and_axes_fail_before_launch(backend):
    ty = LLVMNDArrayType(LLVMInt, 2)
    run, _, _ = compile_plan(backend, "fun a => fun b => NDArray_zipWith a b (fun x => fun y => x + y)", [ty, ty], ty)
    with pytest.raises(ValueError, match="identical shapes"):
        run(full((2, 3), 1), full((3, 2), 1))
    run, _, _ = compile_plan(
        backend, "fun a => fun axis => NDArray_reduce_axis a axis (fun x => fun y => x + y) 0", [ty, LLVMInt], ty
    )
    with pytest.raises(IndexError, match="axis"):
        run(full((2, 3), 1), 2)


def test_async_map_chain_has_one_upload_and_one_host_boundary(cuda, monkeypatch):
    from aeon.llvm.core import Backend
    from aeon.llvm.cuda.converter import CUDALLVMIRGenerator
    from aeon.llvm.cuda.lowerer import CUDALLVMLowerer

    backend = Backend(cuda, CUDALLVMIRGenerator(), CUDALLVMLowerer())
    ty = LLVMNDArrayType(LLVMInt, 1)
    run, _, _ = compile_plan(backend, "fun a => NDArray_map a (fun x => x + 1)", [ty], ty)
    array = NDArray(ManagedArray(list(range(1025))), (1025,))
    uploads, downloads, syncs, allocations = [], [], [], []
    for name, calls in [
        ("cuMemcpyHtoD_v2", uploads),
        ("cuMemcpyDtoH_v2", downloads),
        ("cuCtxSynchronize", syncs),
        ("cuMemAlloc_v2", allocations),
    ]:
        original = getattr(cuda.libcuda, name)

        def spy(*args, original=original, calls=calls):
            calls.append(args)
            return original(*args)

        monkeypatch.setattr(cuda.libcuda, name, spy)
    for _ in range(10):
        array = run(array)
    assert len(uploads) == 1 and uploads[0][2] == 1025 * 4
    assert not downloads and not syncs
    assert len(allocations) <= 3  # Input and two descriptors; the pool serves later calls.
    assert array.data == [i + 10 for i in range(1025)]
    assert len(syncs) == 1 and len(downloads) == 1
    cuda.close()


def test_scratch_buffers_are_reused(cuda, monkeypatch):
    from aeon.llvm.core import Backend
    from aeon.llvm.cuda.converter import CUDALLVMIRGenerator
    from aeon.llvm.cuda.lowerer import CUDALLVMLowerer

    backend = Backend(cuda, CUDALLVMIRGenerator(), CUDALLVMLowerer())
    ty = LLVMNDArrayType(LLVMInt, 1)
    run, _, _ = compile_plan(backend, "fun a => NDArray_scan a (fun x => fun y => x + y) 0", [ty], ty)
    array = full((257,), 0)
    run(array)
    original, allocations = cuda.libcuda.cuMemAlloc_v2, []

    def allocate(*args):
        allocations.append(args)
        return original(*args)

    monkeypatch.setattr(cuda.libcuda, "cuMemAlloc_v2", allocate)
    for _ in range(5):
        run(array)
    assert not allocations
    assert array.data == [0] * 257
    cuda.close()


def test_deferred_failure_poisoning(cuda, monkeypatch):
    from aeon.llvm.core import Backend
    from aeon.llvm.cuda.converter import CUDALLVMIRGenerator
    from aeon.llvm.cuda.lowerer import CUDALLVMLowerer

    backend = Backend(cuda, CUDALLVMIRGenerator(), CUDALLVMLowerer())
    ty = LLVMNDArrayType(LLVMInt, 1)
    run, _, _ = compile_plan(backend, "fun a => NDArray_map a (fun x => x + 1)", [ty], ty)
    array = run(full((17,), 2))
    original = cuda.libcuda.cuCtxSynchronize

    def fail():
        original()
        return 1

    monkeypatch.setattr(cuda.libcuda, "cuCtxSynchronize", fail)
    with pytest.raises(CUDAExecutionError, match="Deferred"):
        array.get(0)
    with pytest.raises(RuntimeError, match="unavailable"):
        array.get(0)
    array.discard()


def test_surface_pipeline_example(cuda, monkeypatch, capsys):
    from aeon.facade.driver import AeonConfig, AeonDriver
    from aeon.synthesis.uis.api import SilentSynthesisUI

    from aeon.llvm.core import Backend
    from aeon.llvm.cuda.converter import CUDALLVMIRGenerator
    from aeon.llvm.cuda.lowerer import CUDALLVMLowerer

    def initialize(pipeline):
        pipeline.cuda_initialized = True
        pipeline.register_backend("cuda", Backend(cuda, CUDALLVMIRGenerator(), CUDALLVMLowerer()))

    monkeypatch.setattr(MultiBackendPipeline, "_initialize_cuda_backend", initialize)
    path = Path("examples/llvm/gpu/array_pipeline.ae")
    driver = AeonDriver(AeonConfig(synthesizer="none", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0))
    # The driver exercises library signatures, linearity, method desugaring, and planning.
    assert not driver.parse(aeon_code=path.read_text())
    driver.run()
    assert capsys.readouterr().out.strip() == "15426"


def test_iteration_reuses_two_buffers_and_expires_borrows(cuda, monkeypatch):
    from aeon.llvm.core import Backend
    from aeon.llvm.cuda.converter import CUDALLVMIRGenerator
    from aeon.llvm.cuda.lowerer import CUDALLVMLowerer
    from aeon.llvm.llvm_ast import LLVMPointerType

    backend = Backend(cuda, CUDALLVMIRGenerator(), CUDALLVMLowerer())
    ty = LLVMNDArrayType(LLVMInt, 2)
    run, _, _ = compile_plan(
        backend,
        "fun xs => fun out => NDArray_map_rows out (fun i => fun row => NDArray_set1 row 0 (get xs i + 1))",
        [LLVMPointerType(LLVMInt), ty],
        ty,
    )
    allocations, uploads, syncs, downloads = [], [], [], []
    for name, calls in [
        ("cuMemAlloc_v2", allocations),
        ("cuMemcpyHtoD_v2", uploads),
        ("cuCtxSynchronize", syncs),
        ("cuMemcpyDtoH_v2", downloads),
    ]:
        original = getattr(cuda.libcuda, name)

        def spy(*args, original=original, calls=calls):
            calls.append(args)
            return original(*args)

        monkeypatch.setattr(cuda.libcuda, name, spy)
    views = []

    def step(i):
        def source(view):
            views.append(view)
            return lambda destination: run(view, destination)

        return source

    array = full((257, 1), 4)
    output = array.iterate(10, 0, step)
    assert len([call for call in allocations if call[1] >= 257 * 4]) == 2
    assert len(uploads) == 1 and not syncs and not downloads
    for view in views:
        with pytest.raises(ValueError, match="expired"):
            len(view)
    assert output.data == [14] * 257
    assert len(syncs) == 1
    cuda.close()


def test_iteration_checks_ownership_and_shape():
    array = full((3, 2), 4)
    with pytest.raises(ValueError, match="destination"):
        array.iterate(1, 0, lambda step: lambda view: lambda output: full((3, 2), 0))


@pytest.mark.parametrize("mode", ["interpreted", "cpu"])
def test_surface_pipeline_portability(mode, capsys):
    from aeon.facade.driver import AeonConfig, AeonDriver
    from aeon.synthesis.uis.api import SilentSynthesisUI

    source = Path("examples/llvm/gpu/array_pipeline.ae").read_text()
    source = source.replace("@gpu\n", "@llvm\n" if mode == "cpu" else "")
    driver = AeonDriver(AeonConfig(synthesizer="none", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0))
    assert not driver.parse(aeon_code=source)
    driver.run()
    assert capsys.readouterr().out.strip() == "15426"


@pytest.mark.parametrize(
    "element,values,callback,initial",
    [
        (LLVMFloat, [-2.5, 3.0, -1.25] * 100, "fun x => fun y => if x < y then x else y", 100.0),
        (LLVMDouble, [-2.5, 3.0, -1.25] * 100, "fun x => fun y => if x > y then x else y", -100.0),
        (LLVMBool, [True, True, False] * 100, "fun x => fun y => x && y", True),
    ],
)
def test_scan_generic_combiners(backend, element, values, callback, initial):
    ty = LLVMNDArrayType(element, 1)
    run, _, _ = compile_plan(backend, f"fun a => fun z => NDArray_scan a ({callback}) z", [ty, element], ty)
    combine = min if element == LLVMFloat else max if element == LLVMDouble else lambda x, y: x and y
    acc, expected = initial, []
    for value in values:
        acc = combine(acc, value)
        expected.append(acc)
    assert run(NDArray(values.copy(), (len(values),)), initial).data == expected


def test_axis_preserves_order_across_lane_chunks(backend):
    ty = LLVMNDArrayType(LLVMInt, 2)
    run, _, _ = compile_plan(backend, "fun a => NDArray_reduce_axis a 1 (fun x => fun y => y) 19", [ty], ty)
    assert run(NDArray(list(range(2 * 65537)), (2, 65537))).data == [65536, 131073]


def test_map_rounds_intermediate_float_before_fusion(backend):
    ty = LLVMNDArrayType(LLVMFloat, 1)
    run, _, _ = compile_plan(
        backend, "fun a => NDArray_map (NDArray_map a (fun x => x + 1.0)) (fun x => x - 16777216.0)", [ty], ty
    )
    assert run(full((257,), 16777216.0)).data == [0.0] * 257


@pytest.mark.parametrize("failure", ["cuMemHostAlloc", "cuMemcpyHtoDAsync_v2", "cuLaunchKernel"])
def test_async_setup_failures_release_staging(cuda, monkeypatch, failure):
    from aeon.llvm.core import Backend
    from aeon.llvm.cuda.converter import CUDALLVMIRGenerator
    from aeon.llvm.cuda.lowerer import CUDALLVMLowerer
    from aeon.llvm.cuda.array_runtime import runtime

    backend = Backend(cuda, CUDALLVMIRGenerator(), CUDALLVMLowerer())
    ty = LLVMNDArrayType(LLVMInt, 1)
    run, _, _ = compile_plan(backend, "fun a => NDArray_map a (fun x => x + 1)", [ty], ty)
    array = full((17,), 4)
    # Configure ctypes APIs before replacing the function under test.
    runtime(cuda)
    with monkeypatch.context() as patch:
        patch.setattr(cuda.libcuda, failure, lambda *args: 1)
        with pytest.raises(CUDAExecutionError):
            run(array)
    assert not runtime(cuda).pinned
    array.fill(4)
    assert run(array).data == [5] * 17
    cuda.close()
    assert runtime(cuda).cached == 0


def test_empty_submissions_bound_pinned_staging(cuda):
    from aeon.llvm.core import Backend
    from aeon.llvm.cuda.converter import CUDALLVMIRGenerator
    from aeon.llvm.cuda.lowerer import CUDALLVMLowerer
    from aeon.llvm.cuda.array_runtime import runtime

    backend = Backend(cuda, CUDALLVMIRGenerator(), CUDALLVMLowerer())
    ty = LLVMNDArrayType(LLVMInt, 1)
    run, _, _ = compile_plan(backend, "fun a => NDArray_map a (fun x => x + 1)", [ty], ty)
    array = full((0,), 4)
    for _ in range(260):
        run(array)
    assert len(runtime(cuda).pinned) < 512
    cuda.close()


def test_materialized_zero_initialization_is_not_reapplied(cuda):
    from aeon.llvm.core import Backend
    from aeon.llvm.cuda.converter import CUDALLVMIRGenerator
    from aeon.llvm.cuda.lowerer import CUDALLVMLowerer

    backend = Backend(cuda, CUDALLVMIRGenerator(), CUDALLVMLowerer())
    ty = LLVMNDArrayType(LLVMInt, 1)
    run, _, _ = compile_plan(backend, "fun a => NDArray_map a (fun x => x + 2)", [ty], ty)
    array = run(full((257,), 0))
    cuda.close()
    assert run(array).data == [4] * 257
    cuda.close()
