"""Parallel map/zip, axis folds, and hierarchical scans over the normal LLVM AST."""

import llvmlite.ir as ir
from aeon.llvm.array_kernels import data_pointer
from aeon.llvm.ndarray import field, element_count
from aeon.llvm.utils import sanitize_name
from aeon.llvm.cuda.reduction import REDUCTION_THREADS


def barrier(generator):
    name = "llvm.nvvm.barrier0"
    function = generator.module.globals.get(name)
    if function is None:
        function = ir.Function(generator.module, ir.FunctionType(ir.VoidType(), []), name=name)
    generator.builder.call(function, [])


def tile(generator, scalar):
    value = ir.GlobalVariable(
        generator.module,
        ir.ArrayType(scalar, REDUCTION_THREADS),
        name=f"array_shared_{len(generator.module.globals)}",
        addrspace=3,
    )
    value.linkage = "internal"
    value.initializer = ir.Constant(value.type.pointee, ir.Undefined)
    return value


def coordinates(generator):
    b = generator.builder
    lane = b.call(generator._get_cuda_intrinsic("tid.x"), [])
    block = b.call(generator._get_cuda_intrinsic("ctaid.x"), [])
    return lane, block, b.add(b.mul(block, ir.Constant(ir.IntType(32), REDUCTION_THREADS)), lane)


def block_scan(generator, callback, source, count, output, totals):
    b, i32 = generator.builder, ir.IntType(32)
    zero, one = ir.Constant(i32, 0), ir.Constant(i32, 1)
    lane, block, index = coordinates(generator)
    scalar = source.type.pointee
    first, second = tile(generator, scalar), tile(generator, scalar)
    valid = b.icmp_unsigned("<", index, count)
    slot = b.gep(first, [zero, lane])
    b.store(ir.Constant(scalar, 0), slot)
    with b.if_then(valid):
        b.store(b.load(b.gep(source, [index])), slot)
    barrier(generator)
    offset = 1
    while offset < REDUCTION_THREADS:
        slot, target = b.gep(first, [zero, lane]), b.gep(second, [zero, lane])
        b.store(b.load(slot), target)
        with b.if_then(b.and_(valid, b.icmp_unsigned(">=", lane, ir.Constant(i32, offset)))):
            previous = b.load(b.gep(first, [zero, b.sub(lane, ir.Constant(i32, offset))]))
            b.store(generator.apply_callback(callback, [previous, b.load(slot)], scalar), target)
        barrier(generator)
        first, second = second, first
        offset *= 2
    with b.if_then(valid):
        value = b.load(b.gep(first, [zero, lane]))
        b.store(value, b.gep(output, [index]))
        last = b.or_(
            b.icmp_unsigned("==", lane, ir.Constant(i32, REDUCTION_THREADS - 1)),
            b.icmp_unsigned("==", b.add(index, one), count),
        )
        with b.if_then(last):
            b.store(value, b.gep(totals, [block]))


def emit_axis(generator, node):
    b, i32 = generator.builder, ir.IntType(32)
    zero = ir.Constant(i32, 0)
    lane, block, _ = coordinates(generator)
    source = node.args[0].accept(generator)
    data, output = data_pointer(generator, node.args[0]), data_pointer(generator, node.array)
    scalar = output.type.pointee
    axis = node.args[1].accept(generator)
    length = b.trunc(b.load(field(b, source, 3, axis)), i32)
    stride = b.trunc(b.load(field(b, source, 4, axis)), i32)
    # Consecutive chunks per lane preserve order for associative, noncommutative folds.
    threads = ir.Constant(i32, REDUCTION_THREADS)
    chunk = b.add(b.udiv(length, threads), b.zext(b.icmp_unsigned("!=", b.urem(length, threads), zero), i32))
    start_j = b.mul(lane, chunk)
    remaining = b.sub(length, start_j)
    valid = b.icmp_unsigned("<", start_j, length)
    local_count = b.select(valid, b.select(b.icmp_unsigned("<", remaining, chunk), remaining, chunk), zero)
    start = b.add(b.mul(b.udiv(block, stride), b.mul(length, stride)), b.urem(block, stride))
    callback, initial_term = node.args[-2:]
    shared = tile(generator, scalar)
    slot = b.gep(shared, [zero, lane])
    b.store(ir.Constant(scalar, 0), slot)
    with b.if_then(valid):
        address = b.add(start, b.mul(start_j, stride))
        b.store(b.load(b.gep(data, [address])), slot)

    def combine(j):
        with b.if_then(b.icmp_unsigned(">", j, zero)):
            address = b.add(start, b.mul(b.add(start_j, j), stride))
            value = b.load(b.gep(data, [address]))
            b.store(generator.apply_callback(callback, [b.load(slot), value], scalar), slot)

    generator.to_ir_loop(local_count, "axis_chunk", combine)
    barrier(generator)
    step = 1
    while step < REDUCTION_THREADS:
        neighbor = b.add(lane, ir.Constant(i32, step))
        active = b.and_(
            b.icmp_unsigned("==", b.urem(lane, ir.Constant(i32, step * 2)), zero),
            b.icmp_unsigned("<", b.mul(neighbor, chunk), length),
        )
        with b.if_then(active):
            value = b.load(b.gep(shared, [zero, neighbor]))
            b.store(generator.apply_callback(callback, [b.load(slot), value], scalar), slot)
        barrier(generator)
        step *= 2
    with b.if_then(b.icmp_unsigned("==", lane, zero)):
        initial = generator._coerce_to_type(initial_term.accept(generator), scalar)
        with b.if_else(b.icmp_unsigned("==", length, zero)) as (empty, nonempty):
            with empty:
                b.store(initial, b.gep(output, [block]))
            with nonempty:
                b.store(generator.apply_callback(callback, [initial, b.load(slot)], scalar), b.gep(output, [block]))


def emit_array_wrappers(generator, function):
    node = function.body
    name = sanitize_name(function.name)
    signature = [generator.to_ir_type(ty) for ty in function.arg_types]
    scalar = generator.to_ir_type(node.type.element_type)
    op = node.op.removesuffix("_into")
    entries = [("kernel", [])]
    if op.startswith("scan"):
        entries = [
            ("kernel", [scalar.as_pointer(), ir.IntType(32), scalar.as_pointer(), scalar.as_pointer()]),
            ("offsets", [scalar.as_pointer(), scalar.as_pointer(), ir.IntType(32)]),
            ("seed", [scalar.as_pointer()]),
        ]
    for suffix, extras in entries:
        kernel = ir.Function(
            generator.module, ir.FunctionType(ir.VoidType(), signature + extras), name=name + "__" + suffix
        )
        generator._add_kernel_metadata(kernel)
        old = generator.builder, generator.env, generator.refinement_env
        generator.builder = b = ir.IRBuilder(kernel.append_basic_block("entry"))
        generator.env = {sanitize_name(n): arg for n, arg in zip(function.arg_names, kernel.args)}
        generator.refinement_env = dict(zip(function.arg_names, kernel.args))
        try:
            if op == "reduce_axis":
                emit_axis(generator, node)
            elif op.startswith("scan"):
                callback = node.args[-2]
                if suffix == "kernel":
                    block_scan(generator, callback, *kernel.args[-4:])
                elif suffix == "offsets":
                    data, parent, count = kernel.args[-3:]
                    lane, block, index = coordinates(generator)
                    valid = b.and_(
                        b.icmp_unsigned("<", index, count), b.icmp_unsigned(">", block, ir.Constant(ir.IntType(32), 0))
                    )
                    with b.if_then(valid):
                        left = b.load(b.gep(parent, [b.sub(block, ir.Constant(ir.IntType(32), 1))]))
                        ptr = b.gep(data, [index])
                        b.store(generator.apply_callback(callback, [left, b.load(ptr)], scalar), ptr)
                else:
                    output = data_pointer(generator, node.array)
                    count = b.trunc(element_count(b, node.array.accept(generator), node.type.rank), ir.IntType(32))
                    _, _, index = coordinates(generator)
                    with b.if_then(b.icmp_unsigned("<", index, count)):
                        initial = generator._coerce_to_type(node.args[-1].accept(generator), scalar)
                        pointer = b.gep(output, [index])
                        if op == "scan_exclusive":
                            with b.if_else(b.icmp_unsigned("==", index, ir.Constant(ir.IntType(32), 0))) as (
                                first,
                                rest,
                            ):
                                with first:
                                    b.store(initial, pointer)
                                with rest:
                                    value = b.load(
                                        b.gep(kernel.args[-1], [b.sub(index, ir.Constant(ir.IntType(32), 1))])
                                    )
                                    b.store(generator.apply_callback(callback, [initial, value], scalar), pointer)
                        else:
                            value = b.load(b.gep(kernel.args[-1], [index]))
                            b.store(generator.apply_callback(callback, [initial, value], scalar), pointer)
            else:
                output = data_pointer(generator, node.array)
                data = data_pointer(generator, node.args[0])
                other = data_pointer(generator, node.args[1]) if op == "zipWith" else None
                count = b.trunc(element_count(b, node.array.accept(generator), node.type.rank), ir.IntType(32))
                _, _, index = coordinates(generator)
                with b.if_then(b.icmp_unsigned("<", index, count)):
                    values = [b.load(b.gep(data, [index]))]
                    if other is not None:
                        values.append(b.load(b.gep(other, [index])))
                    b.store(generator.apply_callback(node.args[-1], values, scalar), b.gep(output, [index]))
            b.ret_void()
        finally:
            generator.builder, generator.env, generator.refinement_env = old
