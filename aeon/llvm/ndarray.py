"""Shared NDArray descriptor ABI and indexing/reshape lowering for CPU and CUDA."""

from __future__ import annotations

import ctypes
import math
from typing import Any

import llvmlite.ir as ir

from aeon.bindings.ndarray import NDArray, contiguous_strides, validate_shape
from aeon.llvm.llvm_ast import LLVMFunction, LLVMNDArrayOp, LLVMNDArrayType
from aeon.llvm.utils import sanitize_name


class NDArrayDescriptor(ctypes.Structure):
    _fields_ = [
        ("data", ctypes.c_void_p),
        ("offset", ctypes.c_int64),
        ("rank", ctypes.c_int64),
        ("shape", ctypes.c_int64 * 3),
        ("strides", ctypes.c_int64 * 3),
        ("error", ctypes.c_int64),
    ]


def pack_array(array: NDArray, ty: LLVMNDArrayType, ctype: Any) -> tuple[NDArrayDescriptor, Any]:
    if not isinstance(array, NDArray) or array.rank != ty.rank:
        raise ValueError(f"Expected a rank-{ty.rank} NDArray")
    validate_shape(array.shape)
    if len(array.data) != math.prod(array.shape):
        raise ValueError("NDArray shape must match its element count")
    buffer = (ctype * array.elements)(*array.data)
    descriptor = NDArrayDescriptor(
        ctypes.addressof(buffer),
        0,
        array.rank,
        (ctypes.c_int64 * 3)(*(array.shape + (1,) * (3 - array.rank))),
        (ctypes.c_int64 * 3)(*(array.strides + (1,) * (3 - array.rank))),
        0,
    )
    return descriptor, buffer


def descriptor_shape(descriptor: NDArrayDescriptor, array: NDArray, data_address: int) -> tuple[int, ...]:
    if descriptor.error == 1:
        raise IndexError("NDArray index is out of bounds")
    if descriptor.error:
        raise ValueError("Incompatible NDArray reshape")
    if descriptor.data != data_address or descriptor.offset != 0 or not 1 <= descriptor.rank <= 3:
        raise ValueError("Kernel returned an invalid NDArray descriptor")
    shape = validate_shape(tuple(descriptor.shape[: descriptor.rank]))
    if math.prod(shape) != array.elements or tuple(descriptor.strides[: descriptor.rank]) != contiguous_strides(shape):
        raise ValueError("Kernel changed NDArray storage or returned a non-contiguous descriptor")
    return shape


def finish_array(array: NDArray, shape: tuple[int, ...], ty: LLVMNDArrayType) -> NDArray:
    if len(shape) != ty.rank:
        raise ValueError("Kernel result rank does not match its declared NDArray type")
    return array if shape == array.shape else array.reshape(shape)


def field(builder: ir.IRBuilder, array: ir.Value, index: int, axis: ir.Value | None = None) -> ir.Value:
    indices = [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), index)]
    if axis is not None:
        indices.append(axis)
    return builder.gep(array, indices)


def as_i64(builder: ir.IRBuilder, value: ir.Value) -> ir.Value:
    return builder.sext(value, ir.IntType(64)) if value.type.width < 64 else value


def axis_value(builder: ir.IRBuilder, array: ir.Value, index: int, axis: int) -> ir.Value:
    return builder.load(field(builder, array, index, ir.Constant(ir.IntType(32), axis)))


def element_count(builder: ir.IRBuilder, array: ir.Value, rank: int) -> ir.Value:
    count = ir.Constant(ir.IntType(64), 1)
    for axis in range(rank):
        count = builder.mul(count, axis_value(builder, array, 3, axis))
    return count


def element_pointer(builder: ir.IRBuilder, array: ir.Value, indices: list[ir.Value]) -> ir.Value:
    offset = builder.load(field(builder, array, 1))
    for axis, index in enumerate(indices):
        offset = builder.add(offset, builder.mul(as_i64(builder, index), axis_value(builder, array, 4, axis)))
    data = builder.load(field(builder, array, 0))
    return builder.gep(data, [offset])


def emit_row(generator: Any, node: LLVMNDArrayOp, array: ir.Value, index: ir.Value, row: ir.Value) -> None:
    """Inline a callback with a private descriptor pointing at one disjoint row."""
    callback = node.args[0]
    assert isinstance(callback, LLVMFunction)
    builder = generator.builder
    i64 = ir.IntType(64)
    zero, one = ir.Constant(i64, 0), ir.Constant(i64, 1)
    cols = axis_value(builder, array, 3, 1)
    offset = builder.add(builder.load(field(builder, array, 1)), builder.mul(as_i64(builder, index), cols))
    builder.store(builder.load(field(builder, array, 0)), field(builder, row, 0))
    builder.store(offset, field(builder, row, 1))
    builder.store(one, field(builder, row, 2))
    builder.store(zero, field(builder, row, 5))
    for axis in range(3):
        coordinate = ir.Constant(ir.IntType(32), axis)
        builder.store(cols if axis == 0 else one, field(builder, row, 3, coordinate))
        builder.store(one, field(builder, row, 4, coordinate))
    old_env, old_refinements = generator.env, generator.refinement_env
    index32 = builder.trunc(index, ir.IntType(32)) if index.type.width > 32 else index
    bindings = dict(zip(callback.arg_names, [index32, row]))
    generator.env = old_env | {sanitize_name(name): value for name, value in bindings.items()}
    generator.refinement_env = old_refinements | bindings
    result = callback.body.accept(generator)
    generator.env, generator.refinement_env = old_env, old_refinements
    error = builder.load(field(builder, row, 5))
    valid = builder.icmp_unsigned("==", result, row)
    valid = builder.and_(valid, builder.icmp_unsigned("==", builder.load(field(builder, row, 2)), one))
    valid = builder.and_(valid, builder.icmp_unsigned("==", axis_value(builder, row, 3, 0), cols))
    valid = builder.and_(valid, builder.icmp_unsigned("==", builder.load(field(builder, row, 1)), offset))
    valid = builder.and_(valid, builder.icmp_unsigned("==", axis_value(builder, row, 4, 0), one))
    valid = builder.and_(
        valid, builder.icmp_unsigned("==", builder.load(field(builder, row, 0)), builder.load(field(builder, array, 0)))
    )
    error = builder.select(valid, error, ir.Constant(i64, 2))
    with builder.if_then(builder.icmp_unsigned("!=", error, zero)):
        # Each row owns its local error flag. Propagate the first failure into
        # the shared parent descriptor without racing other failing rows.
        builder.cmpxchg(field(builder, array, 5), zero, error, "monotonic", "monotonic")


def emit_operation(generator: Any, node: LLVMNDArrayOp) -> ir.Value | None:
    generator._is_top_level = False
    array = node.array.accept(generator)
    if node.op == "map_rows":
        row = generator.builder.alloca(array.type.pointee, name="row_descriptor")
        count = generator.builder.trunc(axis_value(generator.builder, array, 3, 0), ir.IntType(32))
        generator.to_ir_loop(count, "map_rows", lambda index: emit_row(generator, node, array, index, row))
        return array
    args = [arg.accept(generator) for arg in node.args]
    builder = generator.builder
    array_type = node.array.type
    assert isinstance(array_type, LLVMNDArrayType)
    zero64 = ir.Constant(ir.IntType(64), 0)
    one64 = ir.Constant(ir.IntType(64), 1)

    if node.op == "discard":
        return None
    if node.op in {"elements", "count"}:
        return builder.trunc(element_count(builder, array, array_type.rank), ir.IntType(32))
    if node.op == "ndim":
        return builder.trunc(builder.load(field(builder, array, 2)), ir.IntType(32))

    if node.op in {"dimension_size", "dimension"} or node.op.startswith(("get", "set")):
        indices = [
            as_i64(builder, arg)
            for arg in (args[:1] if node.op in {"dimension_size", "dimension"} else args[: array_type.rank])
        ]
        valid = ir.Constant(ir.IntType(1), 1)
        for axis, index in enumerate(indices):
            size = (
                ir.Constant(ir.IntType(64), array_type.rank)
                if node.op in {"dimension_size", "dimension"}
                else axis_value(builder, array, 3, axis)
            )
            bound = builder.and_(builder.icmp_signed(">=", index, zero64), builder.icmp_signed("<", index, size))
            valid = builder.and_(valid, bound)
        scalar_result = not node.op.startswith("set")
        value_type = generator.to_ir_type(node.type) if scalar_result else None
        with builder.if_else(valid) as (yes, no):
            with yes:
                if node.op in {"dimension_size", "dimension"}:
                    value = builder.trunc(builder.load(field(builder, array, 3, indices[0])), ir.IntType(32))
                else:
                    pointer = element_pointer(builder, array, indices)
                    if scalar_result:
                        value = builder.load(pointer)
                    else:
                        value = generator._coerce_to_type(args[-1], array_type.element_type.to_ir())
                        builder.store(value, pointer)
                success_block = builder.block
            with no:
                builder.store(one64, field(builder, array, 5))
                failure_block = builder.block
        if scalar_result:
            result = builder.phi(value_type)
            result.add_incoming(value, success_block)
            result.add_incoming(ir.Constant(value_type, 0), failure_block)
            return result
        return array

    if node.op == "fill":
        value = generator._coerce_to_type(args[0], array_type.element_type.to_ir())
        count = builder.trunc(element_count(builder, array, array_type.rank), ir.IntType(32))
        data = builder.load(field(builder, array, 0))
        offset = builder.load(field(builder, array, 1))

        def fill_one(index):
            pointer = builder.gep(data, [builder.add(offset, as_i64(builder, index))])
            builder.store(value, pointer)

        generator.to_ir_loop(count, "ndarray_fill", fill_one)
        return array

    if node.op in {"to_1d", "from_1d2", "from_1d3"}:
        assert isinstance(node.type, LLVMNDArrayType)
        shape = (
            [element_count(builder, array, array_type.rank)]
            if node.op == "to_1d"
            else [as_i64(builder, arg) for arg in args]
        )
        valid = ir.Constant(ir.IntType(1), 1)
        count = one64
        multiply = generator.module.globals.get("llvm.umul.with.overflow.i64")
        if multiply is None:
            i64 = ir.IntType(64)
            multiply = ir.Function(
                generator.module,
                ir.FunctionType(ir.LiteralStructType([i64, ir.IntType(1)]), [i64, i64]),
                name="llvm.umul.with.overflow.i64",
            )
        for size in shape:
            valid = builder.and_(valid, builder.icmp_signed(">=", size, zero64))
            valid = builder.and_(valid, builder.icmp_signed("<=", size, ir.Constant(ir.IntType(64), 2**31 - 1)))
            product = builder.call(multiply, [count, size])
            count = builder.extract_value(product, 0)
            valid = builder.and_(valid, builder.not_(builder.extract_value(product, 1)))
        valid = builder.and_(valid, builder.icmp_unsigned("==", count, element_count(builder, array, array_type.rank)))
        with builder.if_else(valid) as (yes, no):
            with yes:
                builder.store(ir.Constant(ir.IntType(64), node.type.rank), field(builder, array, 2))
                stride = one64
                for axis in reversed(range(3)):
                    size = shape[axis] if axis < len(shape) else one64
                    builder.store(size, field(builder, array, 3, ir.Constant(ir.IntType(32), axis)))
                    builder.store(stride, field(builder, array, 4, ir.Constant(ir.IntType(32), axis)))
                    stride = builder.mul(stride, size)
            with no:
                builder.store(ir.Constant(ir.IntType(64), 2), field(builder, array, 5))
        return array

    raise ValueError(f"Unsupported compiled NDArray operation: {node.op}")
