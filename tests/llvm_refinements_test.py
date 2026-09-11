"""Refinement hints must be scoped, representable, and valid on both targets."""

import ctypes

import llvmlite.binding as llvm
import pytest

from aeon.core.parser import parse_term, parse_type
from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
from aeon.llvm.cpu.converter import CPULLVMIRGenerator
from aeon.llvm.cpu.lowerer import CPULLVMLowerer
from aeon.llvm.cuda.converter import CUDALLVMIRGenerator
from aeon.llvm.cuda.executor import CUDAExecutionEngine
from aeon.llvm.llvm_ast import LLVMFunction, LLVMFunctionType, LLVMInt, LLVMVar, LLVMRefinedValue
from aeon.llvm.optimization import optimize_module
from aeon.llvm.refinements import integer_range
from aeon.llvm.utils import to_llvm_type
from aeon.utils.name import Name


def lower(body, signature, name="test"):
    f = CPULLVMLowerer().lower(parse_term(body), expected_type=to_llvm_type(parse_type(signature)))
    f.name = Name(name, 0)
    return f


def optimized(code):
    tm = llvm.Target.from_default_triple().create_target_machine()
    module = llvm.parse_assembly(code)
    optimize_module(module, tm)
    return str(module)


def test_nonnegative_parameter_removes_signed_division_correction():
    function = lower("fun x => x / 2", "(different:{v:Int | v >= 0}) -> Int")
    plain = CPULLVMIRGenerator(use_refinements=False).generate_ir([function])
    hinted = CPULLVMIRGenerator().generate_ir([function])
    assert 'call void @"llvm.assume"' in hinted
    assert "llvm.assume" not in plain
    assert "lshr i32" in optimized(hinted)
    assert "sdiv i32" in optimized(plain)


def test_dependent_parameter_names_are_mapped_to_actual_lambda_binders():
    f = lower("fun a => fun b => b / 2", "(n:Int) -> (x:{v:Int | v >= n}) -> Int")
    code = CPULLVMIRGenerator().generate_ir([f])
    assert 'icmp sge i32 %"b", %"a"' in code
    llvm.parse_assembly(code).verify()


@pytest.mark.parametrize("predicate", ["v * v >= 0", "v >= 2147483648", "v > 0 || v * v >= 0"])
def test_unsupported_or_unrepresentable_predicates_are_not_assumed(predicate):
    f = lower("fun x => x", f"(x:{{v:Int | {predicate}}}) -> Int")
    code = CPULLVMIRGenerator().generate_ir([f])
    assert "llvm.assume" not in code
    llvm.parse_assembly(code).verify()


def test_supported_conjunct_survives_unsupported_arithmetic():
    f = lower("fun x => x", "(x:{v:Int | v >= 0 && v * v >= 0}) -> Int")
    code = CPULLVMIRGenerator().generate_ir([f])
    assert "llvm.assume" in code
    assert "mul i32" not in code


def test_floating_point_refinements_are_not_reinterpreted_as_integer_facts():
    f = lower("fun x => x", "(x:{v:Float | v >= 0.0}) -> Float")
    assert "llvm.assume" not in CPULLVMIRGenerator().generate_ir([f])


@pytest.mark.parametrize("lo,hi", [(-10, 10), (0, 2147483647), (-2147483648, -1)])
def test_range_bounds_use_exclusive_upper_endpoint(lo, hi):
    v = Name("v", 0)
    pred = LiquidApp(
        Name("&&", 0),
        [
            LiquidApp(Name(">=", 0), [LiquidVar(v), LiquidLiteralInt(lo)]),
            LiquidApp(Name("<=", 0), [LiquidVar(v), LiquidLiteralInt(hi)]),
        ],
    )
    assert integer_range(pred, v, 32) == (lo, hi + 1)


def test_range_metadata_attaches_to_fresh_load():
    body = parse_term("fun xs => ((get xs 0) : {v:Int | v >= 0 && v <= 255})")
    f = CPULLVMLowerer().lower(body, expected_type=to_llvm_type(parse_type("(xs:(Vector Int)) -> Int")))
    f.name = Name("load_byte", 0)
    code = CPULLVMIRGenerator().generate_ir([f])
    assert "!range" in code
    assert "i32 0, i32 256" in code
    llvm.parse_assembly(code).verify()


def test_call_return_range_does_not_assume_callee_parameter_names_in_caller():
    from aeon.llvm.llvm_ast import LLVMCall

    contract = parse_type("{r:Int | r >= 0 && r > x}")
    target = LLVMVar(LLVMFunctionType([LLVMInt], LLVMInt), Name("external", 0))
    value = LLVMRefinedValue(
        LLVMInt, LLVMCall(LLVMInt, target, [LLVMVar(LLVMInt, Name("x", 0))]), contract, range_only=True
    )
    f = LLVMFunction(LLVMFunctionType([LLVMInt], LLVMInt), [Name("x", 0)], [LLVMInt], value, Name("caller", 0))
    generator = CPULLVMIRGenerator()
    generator.declare_external(target.name, target.type)
    code = generator.generate_ir([f])
    assert "!range" in code
    assert "llvm.assume" not in code
    llvm.parse_assembly(code).verify()


def test_branch_refinement_does_not_annotate_an_earlier_load():
    f = lower(
        "fun xs => let x = get xs 0 in if x >= 0 then (x : {v:Int | v >= 0}) else x",
        "(xs:(Vector Int)) -> Int",
    )
    code = CPULLVMIRGenerator().generate_ir([f])
    assert "llvm.assume" in code
    assert "!range" not in code
    llvm.parse_assembly(code).verify()


def test_typed_local_remains_a_value_and_preserves_its_refinement():
    f = lower("fun x => let y : {v:Int | v >= 0} = x in y / 2", "(x:Int) -> Int")
    code = CPULLVMIRGenerator().generate_ir([f])
    llvm.parse_assembly(code).verify()
    assert "lshr i32" in optimized(code)


def test_cuda_emits_void_entry_wrapper_and_optimized_device_function():
    f = lower("fun x => x / 2", "(n:{v:Int | v >= 0}) -> Int", "halve")
    code = CUDALLVMIRGenerator().generate_ir([f])
    llvm.parse_assembly(code).verify()
    ptx = CUDAExecutionEngine.__new__(CUDAExecutionEngine)._compile_to_ptx(code)
    assert ".entry halve__kernel" in ptx
    assert "shr.u32" in ptx
    assert "llvm.assume" not in ptx


def test_quicksort_checked_source_sorts_without_mutating_input():
    from pathlib import Path
    from aeon.compilation.compile import compile_and_link
    from aeon.llvm.pipeline import MultiBackendPipeline
    from aeon.llvm.utils import sanitize_name

    path = Path(__file__).resolve().parents[1] / "examples/llvm/functional_quicksort.ae"
    _, core, _, metadata, _, errors = compile_and_link(str(path), is_main=True, is_main_hole=False)
    assert not errors
    pipeline = MultiBackendPipeline(metadata)
    pipeline.compile(core)
    definitions = list(pipeline.compiled_functions_by_backend["cpu"].values())
    name = next(sanitize_name(f.name) for f in definitions if f.name.name == "sort_into")
    for hints in (False, True):
        module = llvm.parse_assembly(CPULLVMIRGenerator(use_refinements=hints).generate_ir(definitions))
        tm = llvm.Target.from_default_triple().create_target_machine()
        optimize_module(module, tm)
        with llvm.create_mcjit_compiler(module, tm) as engine:
            engine.finalize_object()
            sort = ctypes.CFUNCTYPE(
                None, ctypes.POINTER(ctypes.c_int32), ctypes.POINTER(ctypes.c_int32), ctypes.c_int32
            )(engine.get_function_address(name))
            for values in (
                [],
                [1],
                [3, 1, 2],
                [2] * 64,
                list(range(64)),
                list(range(64, 0, -1)),
                [-2147483648, 2147483647, 0, -1, 0],
            ):
                source = (ctypes.c_int32 * len(values))(*values)
                out = (ctypes.c_int32 * len(values))()
                sort(source, out, len(values))
                assert list(out) == sorted(values)
                assert list(source) == values


def test_overflow_cannot_turn_a_mathematical_refinement_into_llvm_ub():
    # With unbounded integers x+1 is positive; at INT_MAX the old LLVM backend
    # wraps. Do not add an assumption that changes that existing behaviour.
    f = lower("fun x => ((x + 1) : {v:Int | v > 0})", "(x:{v:Int | v >= 0}) -> Int")
    code = CPULLVMIRGenerator().generate_ir([f])
    assert "llvm.assume" not in code
    assert "!range" not in code
    llvm.parse_assembly(code).verify()


def test_overflowing_branch_disables_call_result_range_for_whole_module():
    signature = parse_type("(x:Int) -> {r:Int | r >= 0 && r <= 1}")
    callee = lower("fun x => if x + 1 > x then 1 else (0 - 1)", "(x:Int) -> {r:Int | r >= 0 && r <= 1}", "callee")
    caller = CPULLVMLowerer().lower(
        parse_term("fun y => callee y"),
        expected_type=to_llvm_type(parse_type("(y:Int) -> Int")),
        type_env={Name("callee"): to_llvm_type(signature)},
    )
    caller.name = Name("caller", 0)
    # Match parser names so the call resolves to the generated definition.
    callee.name = Name("callee")
    code = CPULLVMIRGenerator().generate_ir([callee, caller])
    assert "!range" not in code
    assert "llvm.assume" not in code
    llvm.parse_assembly(code).verify()


def test_bounded_arithmetic_keeps_refinement_hints():
    f = lower("fun x => ((x + 1) : {v:Int | v > 0})", "(x:{v:Int | v >= 0 && v < 100}) -> Int")
    code = CPULLVMIRGenerator().generate_ir([f])
    assert "llvm.assume" in code
    llvm.parse_assembly(code).verify()
