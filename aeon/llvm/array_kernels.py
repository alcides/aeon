"""CPU loops for planned NDArray operations, using the shared callback compiler."""

import llvmlite.ir as ir
from aeon.llvm.ndarray import field, element_count, as_i64


def data_pointer(generator, term):
    descriptor = term.accept(generator)
    builder = generator.builder
    return builder.gep(builder.load(field(builder, descriptor, 0)), [builder.load(field(builder, descriptor, 1))])


def emit_sequential(generator, node):
    builder = generator.builder
    destination = node.array.accept(generator)
    source_term = node.args[0]
    source = source_term.accept(generator)
    data = data_pointer(generator, source_term)
    output = data_pointer(generator, node.array)
    scalar = output.type.pointee
    count = builder.trunc(element_count(builder, destination, node.type.rank), ir.IntType(32))
    op = node.op.removesuffix("_into")
    if op in {"map", "zipWith"}:
        other = data_pointer(generator, node.args[1]) if op == "zipWith" else None
        callback = node.args[-1]

        def element(index):
            values = [builder.load(builder.gep(data, [index]))]
            if other is not None:
                values.append(builder.load(builder.gep(other, [index])))
            builder.store(generator.apply_callback(callback, values, scalar), builder.gep(output, [index]))

        generator.to_ir_loop(count, op, element)
    else:
        callback, initial_term = node.args[-2:]
        initial = generator._coerce_to_type(initial_term.accept(generator), scalar)
        acc = builder.alloca(scalar, name="accumulator")
        if op.startswith("scan"):
            builder.store(initial, acc)

            def prefix(index):
                value = builder.load(builder.gep(data, [index]))
                before = builder.load(acc)
                after = generator.apply_callback(callback, [before, value], scalar)
                builder.store(after, acc)
                builder.store(before if op == "scan_exclusive" else after, builder.gep(output, [index]))

            generator.to_ir_loop(count, "scan", prefix)
        else:
            axis = node.args[1].accept(generator)
            length = builder.load(field(builder, source, 3, axis))
            stride = builder.load(field(builder, source, 4, axis))

            def reduce_one(index):
                index = as_i64(builder, index)
                start = builder.add(
                    builder.mul(builder.udiv(index, stride), builder.mul(length, stride)), builder.urem(index, stride)
                )
                builder.store(initial, acc)

                def combine(j):
                    address = builder.add(start, builder.mul(as_i64(builder, j), stride))
                    value = builder.load(builder.gep(data, [address]))
                    builder.store(generator.apply_callback(callback, [builder.load(acc), value], scalar), acc)

                generator.to_ir_loop(builder.trunc(length, ir.IntType(32)), "axis", combine)
                builder.store(builder.load(acc), builder.gep(output, [index]))

            generator.to_ir_loop(count, "reduce_axis", reduce_one)
    return destination
