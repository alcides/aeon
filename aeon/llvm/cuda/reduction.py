"""Launch metadata and a common LLVM tree for lambda-based scalar reductions."""

from dataclasses import dataclass

import llvmlite.ir as ir

from aeon.bindings.ndarray import NDArray
from aeon.llvm.llvm_ast import (
    LLVMCast,
    LLVMRefinedValue,
    LLVMVar,
    LLVMLiteral,
    LLVMNDArrayType,
    LLVMVectorReduce,
    LLVMIntType,
    LLVMFloatType,
    LLVMDoubleType,
    LLVMBoolType,
    LLVMPointerType,
)
from aeon.llvm.ndarray import element_count, field
from aeon.llvm.utils import sanitize_name


REDUCTION_THREADS = 256


@dataclass(frozen=True)
class ReductionLaunch:
    array_index: int
    size_index: int | None = None
    constant_size: int | None = None

    def count(self, arguments) -> int:
        array = arguments[self.array_index]
        available = array.elements if isinstance(array, NDArray) else len(array)
        count = (
            arguments[self.size_index]
            if self.size_index is not None
            else self.constant_size
            if self.constant_size is not None
            else available
        )
        if isinstance(count, bool) or not isinstance(count, int) or not 0 <= count <= min(available, 2**31 - 1):
            raise ValueError("Reduction length must be a non-negative Int within the input array")
        return count


def unwrap(value):
    while isinstance(value, (LLVMCast, LLVMRefinedValue)):
        value = value.val if isinstance(value, LLVMCast) else value.value
    return value


def reduction_launch(node, body) -> ReductionLaunch | None:
    if not isinstance(body, LLVMVectorReduce):
        return None
    vector = unwrap(body.v)
    if (
        not isinstance(vector, LLVMVar)
        or vector.name not in node.arg_names
        or not isinstance(vector.type, (LLVMPointerType, LLVMNDArrayType))
    ):
        return None
    element = vector.type.element_type
    if body.type != element or not isinstance(element, (LLVMIntType, LLVMFloatType, LLVMDoubleType, LLVMBoolType)):
        # A general fold may have a different accumulator type; retain its loop.
        return None
    array_index = node.arg_names.index(vector.name)
    if isinstance(vector.type, LLVMNDArrayType):
        return ReductionLaunch(array_index)
    size = unwrap(body.size)
    if isinstance(size, LLVMVar) and size.name in node.arg_names:
        return ReductionLaunch(array_index, size_index=node.arg_names.index(size.name))
    if isinstance(size, LLVMLiteral):
        return ReductionLaunch(array_index, constant_size=size.value)
    return None


def emit_reduction_wrappers(generator, node, body, kernel, builder):
    """Both passes compile the same reducer using the existing expression visitor."""
    scalar = generator.to_ir_type(body.type)
    continuation = ir.Function(
        generator.module,
        ir.FunctionType(
            ir.VoidType(), [*kernel.function_type.args[:-1], scalar.as_pointer(), ir.IntType(32), scalar.as_pointer()]
        ),
        name=kernel.name.removesuffix("__kernel") + "__reduce",
    )
    generator._add_kernel_metadata(continuation)
    for entry, entry_builder, first in (
        (kernel, builder, True),
        (continuation, ir.IRBuilder(continuation.append_basic_block("entry")), False),
    ):
        old_builder, old_env, old_refinements = generator.builder, generator.env, generator.refinement_env
        generator.builder = entry_builder
        generator.env = {sanitize_name(name): value for name, value in zip(node.arg_names, entry.args)}
        generator.refinement_env = dict(zip(node.arg_names, entry.args))
        try:
            if first:
                source = body.v.accept(generator)
                if isinstance(body.v.type, LLVMNDArrayType):
                    count = entry_builder.trunc(element_count(entry_builder, source, body.v.type.rank), ir.IntType(32))
                    source = entry_builder.gep(
                        entry_builder.load(field(entry_builder, source, 0)),
                        [entry_builder.load(field(entry_builder, source, 1))],
                    )
                else:
                    count = body.size.accept(generator)
            else:
                source, count = entry.args[-3:-1]
            initial = generator._coerce_to_type(body.initial.accept(generator), scalar)
            _emit_tree(generator, body.f, source, count, initial, entry.args[-1], scalar)
            entry_builder.ret_void()
        finally:
            generator.builder, generator.env, generator.refinement_env = old_builder, old_env, old_refinements


def _emit_tree(generator, callback, source, count, initial, destination, scalar):
    builder = generator.builder
    i32 = ir.IntType(32)
    zero = ir.Constant(i32, 0)
    lane = builder.call(generator._get_cuda_intrinsic("tid.x"), [])
    block = builder.call(generator._get_cuda_intrinsic("ctaid.x"), [])
    start = builder.mul(block, ir.Constant(i32, REDUCTION_THREADS))
    index = builder.add(start, lane)
    # Shared storage is private to each block. Every lane reaches every barrier.
    shared = ir.GlobalVariable(
        generator.module,
        ir.ArrayType(scalar, REDUCTION_THREADS),
        name=f"reduce_shared_{len(generator.module.globals)}",
        addrspace=3,
    )
    shared.linkage = "internal"
    shared.initializer = ir.Constant(shared.type.pointee, ir.Undefined)
    slot = builder.gep(shared, [zero, lane])
    builder.store(ir.Constant(scalar, 0), slot)
    with builder.if_then(builder.icmp_unsigned("<", index, count)):
        builder.store(builder.load(builder.gep(source, [index])), slot)
    barrier = generator.module.globals.get("llvm.nvvm.barrier0")
    if barrier is None:
        barrier = ir.Function(generator.module, ir.FunctionType(ir.VoidType(), []), name="llvm.nvvm.barrier0")
    builder.call(barrier, [])
    stride = 1
    while stride < REDUCTION_THREADS:
        neighbor = builder.add(lane, ir.Constant(i32, stride))
        active = builder.icmp_unsigned("==", builder.urem(lane, ir.Constant(i32, stride * 2)), zero)
        active = builder.and_(active, builder.icmp_unsigned("<", builder.add(start, neighbor), count))
        with builder.if_then(active):
            right = builder.load(builder.gep(shared, [zero, neighbor]))
            builder.store(generator.apply_callback(callback, [builder.load(slot), right], scalar), slot)
        builder.call(barrier, [])
        stride *= 2
    with builder.if_then(builder.icmp_unsigned("==", lane, zero)):
        with builder.if_else(builder.icmp_unsigned("==", count, zero)) as (empty, nonempty):
            with empty:
                builder.store(initial, builder.gep(destination, [block]))
            with nonempty:
                total = builder.load(slot)
                # Only the final pass applies z; intermediate blocks have no identity requirement.
                with builder.if_else(builder.icmp_unsigned("<=", count, ir.Constant(i32, REDUCTION_THREADS))) as (
                    last,
                    partial,
                ):
                    with last:
                        value = generator.apply_callback(callback, [initial, total], scalar)
                        builder.store(value, builder.gep(destination, [block]))
                    with partial:
                        builder.store(total, builder.gep(destination, [block]))
