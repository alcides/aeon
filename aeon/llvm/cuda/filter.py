"""Stable compaction built from LLVM predicate, block-scan, and scatter entries."""

import llvmlite.ir as ir
import ctypes

from aeon.llvm.llvm_ast import LLVMNDArrayType
from aeon.llvm.ndarray import element_count, field
from aeon.llvm.utils import sanitize_name
from aeon.llvm.cuda.reduction import REDUCTION_THREADS


def source_and_count(generator, body):
    source = body.v.accept(generator)
    if isinstance(body.v.type, LLVMNDArrayType):
        count = generator.builder.trunc(element_count(generator.builder, source, body.v.type.rank), ir.IntType(32))
        source = generator.builder.gep(
            generator.builder.load(field(generator.builder, source, 0)),
            [generator.builder.load(field(generator.builder, source, 1))],
        )
        return source, count
    return source, body.size.accept(generator)


def coordinates(generator):
    builder = generator.builder
    lane = builder.call(generator._get_cuda_intrinsic("tid.x"), [])
    block = builder.call(generator._get_cuda_intrinsic("ctaid.x"), [])
    index = builder.add(builder.mul(block, ir.Constant(ir.IntType(32), REDUCTION_THREADS)), lane)
    return lane, block, index


def block_scan(generator, value, lane):
    """Inclusive scan, with two shared tiles so each round needs one barrier."""
    builder, module = generator.builder, generator.module
    i32 = ir.IntType(32)
    zero = ir.Constant(i32, 0)
    shared = ir.GlobalVariable(
        module, ir.ArrayType(i32, 2 * REDUCTION_THREADS), name=f"filter_scan_shared_{len(module.globals)}", addrspace=3
    )
    shared.linkage = "internal"
    shared.initializer = ir.Constant(shared.type.pointee, ir.Undefined)
    barrier = module.globals.get("llvm.nvvm.barrier0")
    if barrier is None:
        barrier = ir.Function(module, ir.FunctionType(ir.VoidType(), []), name="llvm.nvvm.barrier0")
    builder.store(value, builder.gep(shared, [zero, lane]))
    builder.call(barrier, [])
    base = 0
    stride = 1
    neighbor_slot = builder.alloca(i32, name="scan_neighbor")
    while stride < REDUCTION_THREADS:
        current_index = builder.add(lane, ir.Constant(i32, base))
        current = builder.load(builder.gep(shared, [zero, current_index]))
        builder.store(zero, neighbor_slot)
        with builder.if_then(builder.icmp_unsigned(">=", lane, ir.Constant(i32, stride))):
            neighbor = builder.sub(current_index, ir.Constant(i32, stride))
            builder.store(builder.load(builder.gep(shared, [zero, neighbor])), neighbor_slot)
        base = REDUCTION_THREADS - base
        target = builder.add(lane, ir.Constant(i32, base))
        builder.store(builder.add(current, builder.load(neighbor_slot)), builder.gep(shared, [zero, target]))
        builder.call(barrier, [])
        stride *= 2
    prefix = builder.load(builder.gep(shared, [zero, builder.add(lane, ir.Constant(i32, base))]))
    total = builder.load(builder.gep(shared, [zero, ir.Constant(i32, base + REDUCTION_THREADS - 1)]))
    return prefix, total


def emit_filter_wrappers(generator, node, body, kernel):
    module, i32 = generator.module, ir.IntType(32)
    original_args = list(kernel.function_type.args[:-2])
    scalar = generator.to_ir_type(body.v.type.element_type)
    pointer = i32.as_pointer()
    entries = {
        "scan": [pointer, i32, pointer, pointer],
        "offsets": [pointer, pointer, i32],
        "scatter": [*original_args, pointer, pointer, scalar.as_pointer()],
    }
    helpers = {}
    for suffix, args in entries.items():
        helper = ir.Function(
            module, ir.FunctionType(ir.VoidType(), args), name=kernel.name.removesuffix("__kernel") + "__" + suffix
        )
        generator._add_kernel_metadata(helper)
        helpers[suffix] = helper
    old = generator.builder, generator.env, generator.refinement_env
    try:
        for suffix, entry in [("predicate", kernel), *helpers.items()]:
            builder = ir.IRBuilder(entry.append_basic_block("entry"))
            generator.builder = builder
            generator.env = {sanitize_name(name): value for name, value in zip(node.arg_names, entry.args)}
            generator.refinement_env = dict(zip(node.arg_names, entry.args))
            lane, block, index = coordinates(generator)
            zero, one = ir.Constant(i32, 0), ir.Constant(i32, 1)
            if suffix in {"predicate", "scan"}:
                if suffix == "predicate":
                    source, count = source_and_count(generator, body)
                    positions, totals = entry.args[-2:]
                else:
                    source, count, positions, totals = entry.args
                value = builder.alloca(i32, name="scan_value")
                builder.store(zero, value)
                with builder.if_then(builder.icmp_unsigned("<", index, count)):
                    item = builder.load(builder.gep(source, [index]))
                    if suffix == "predicate":
                        item = builder.zext(generator.apply_callback(body.f, [item], ir.IntType(1)), i32)
                    builder.store(item, value)
                prefix, total = block_scan(generator, builder.load(value), lane)
                with builder.if_then(builder.icmp_unsigned("<", index, count)):
                    builder.store(prefix, builder.gep(positions, [index]))
                with builder.if_then(builder.icmp_unsigned("==", lane, zero)):
                    builder.store(total, builder.gep(totals, [block]))
            elif suffix == "offsets":
                positions, parent, count = entry.args
                valid = builder.and_(builder.icmp_unsigned("<", index, count), builder.icmp_unsigned(">", block, zero))
                with builder.if_then(valid):
                    offset = builder.load(builder.gep(parent, [builder.sub(block, one)]))
                    slot = builder.gep(positions, [index])
                    builder.store(builder.add(builder.load(slot), offset), slot)
            else:
                source, count = source_and_count(generator, body)
                positions, parent, output = entry.args[-3:]
                previous = builder.alloca(i32, name="previous_prefix")
                offset = builder.alloca(i32, name="block_offset")
                with builder.if_then(builder.icmp_unsigned("<", index, count)):
                    builder.store(zero, previous)
                    builder.store(zero, offset)
                    with builder.if_then(builder.icmp_unsigned(">", lane, zero)):
                        builder.store(builder.load(builder.gep(positions, [builder.sub(index, one)])), previous)
                    with builder.if_then(builder.icmp_unsigned(">", block, zero)):
                        builder.store(builder.load(builder.gep(parent, [builder.sub(block, one)])), offset)
                    prefix = builder.load(builder.gep(positions, [index]))
                    with builder.if_then(builder.icmp_unsigned("!=", prefix, builder.load(previous))):
                        target = builder.sub(builder.add(builder.load(offset), prefix), one)
                        builder.store(builder.load(builder.gep(source, [index])), builder.gep(output, [target]))
            builder.ret_void()
    finally:
        generator.builder, generator.env, generator.refinement_env = old


class FilterBuffers:
    """Temporary scan hierarchy; all allocations participate in executor cleanup."""

    def __init__(self, engine, module, name, count, scalar, allocations):
        self.engine, self.module, self.name = engine, module, name
        self.count, self.allocations, self.scalars = count, allocations, []
        self.blocks = max(1, (count + REDUCTION_THREADS - 1) // REDUCTION_THREADS)
        self.positions = self.allocate(max(1, count) * 4)
        self.totals = self.allocate(self.blocks * 4)
        self.output = self.allocate(max(4, count * ctypes.sizeof(scalar)))
        self.final_total = self.totals
        self.levels = []
        remaining = self.blocks
        while remaining > 1:
            blocks = (remaining + REDUCTION_THREADS - 1) // REDUCTION_THREADS
            prefix, totals = self.allocate(remaining * 4), self.allocate(blocks * 4)
            self.levels.append((prefix, totals, remaining))
            self.final_total = totals
            remaining = blocks

    def allocate(self, size):
        from aeon.llvm.cuda.executor import CUDAExecutionError

        pointer = ctypes.c_uint64()
        if self.engine.libcuda.cuMemAlloc_v2(ctypes.byref(pointer), size) != 0:
            raise CUDAExecutionError("cuMemAlloc failed for filter scratch")
        self.allocations.append(pointer)
        return pointer

    def launch(self, suffix, values, count):
        from aeon.llvm.cuda.executor import CUDAExecutionError

        parameters = (ctypes.c_void_p * len(values))(*[ctypes.addressof(value) for value in values])
        function = self.engine._get_function(self.module, self.name + "__" + suffix)
        grid, block = self.engine._launch_dimensions((count,))
        rc = self.engine.libcuda.cuLaunchKernel(function, *grid, *block, 0, None, parameters, None)
        if rc != 0:
            raise CUDAExecutionError(f"cuLaunchKernel failed for filter {suffix}: {self.engine._cuda_error_name(rc)}")

    def remaining_passes(self, original_parameters):
        source = self.totals
        for prefix, totals, count in self.levels:
            size = ctypes.c_int32(count)
            self.scalars.append(size)
            self.launch("scan", [source, size, prefix, totals], count)
            source = totals
        for index in range(len(self.levels) - 2, -1, -1):
            prefix, _, count = self.levels[index]
            size = ctypes.c_int32(count)
            self.scalars.append(size)
            self.launch("offsets", [prefix, self.levels[index + 1][0], size], count)
        block_prefix = self.levels[0][0] if self.levels else self.totals
        # Original arguments already have stable ctypes storage in the executor.
        extras = [self.positions, block_prefix, self.output]
        values = original_parameters + [ctypes.addressof(value) for value in extras]
        parameters = (ctypes.c_void_p * len(values))(*values)
        from aeon.llvm.cuda.executor import CUDAExecutionError

        function = self.engine._get_function(self.module, self.name + "__scatter")
        grid, block = self.engine._launch_dimensions((self.count,))
        rc = self.engine.libcuda.cuLaunchKernel(function, *grid, *block, 0, None, parameters, None)
        if rc != 0:
            raise CUDAExecutionError("cuLaunchKernel failed for filter scatter")
