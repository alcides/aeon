"""Shared filter launch metadata and the CPU entry ABI for dynamic lengths."""

from dataclasses import dataclass
import llvmlite.ir as ir

from aeon.bindings.ndarray import NDArray
from aeon.llvm.llvm_ast import LLVMVar, LLVMCast, LLVMRefinedValue, LLVMLiteral, LLVMVectorFilter, LLVMNDArrayType
from aeon.llvm.utils import sanitize_name


@dataclass(frozen=True)
class FilterLaunch:
    array_index: int
    size_index: int | None = None
    constant_size: int | None = None

    def count(self, arguments):
        array = arguments[self.array_index]
        available = array.elements if isinstance(array, NDArray) else len(array)
        count = arguments[self.size_index] if self.size_index is not None else self.constant_size
        count = available if count is None else count
        if isinstance(count, bool) or not isinstance(count, int) or not 0 <= count <= min(available, 2**31 - 1):
            raise ValueError("Filter length must be a non-negative Int within the input array")
        return count


def filter_launch(node, body):
    if not isinstance(body, LLVMVectorFilter):
        return None
    vector = body.v
    while isinstance(vector, (LLVMCast, LLVMRefinedValue)):
        vector = vector.val if isinstance(vector, LLVMCast) else vector.value
    if not isinstance(vector, LLVMVar) or vector.name not in node.arg_names:
        return None
    index = node.arg_names.index(vector.name)
    if isinstance(vector.type, LLVMNDArrayType):
        return FilterLaunch(index)
    size = body.size
    if isinstance(size, LLVMVar) and size.name in node.arg_names:
        return FilterLaunch(index, size_index=node.arg_names.index(size.name))
    if isinstance(size, LLVMLiteral):
        return FilterLaunch(index, constant_size=size.value)
    return None


def emit_cpu_filter_wrapper(generator, node, body):
    original = generator.module.globals[sanitize_name(node.name)]
    wrapper = ir.Function(
        generator.module,
        ir.FunctionType(
            original.function_type.return_type, [*original.function_type.args, ir.IntType(32).as_pointer()]
        ),
        name=original.name + "__filter",
    )
    old = generator.builder, generator.env, generator.refinement_env, generator._filter_length_out
    generator.builder = ir.IRBuilder(wrapper.append_basic_block("entry"))
    generator.env = {sanitize_name(name): value for name, value in zip(node.arg_names, wrapper.args)}
    generator.refinement_env = dict(zip(node.arg_names, wrapper.args))
    generator._filter_length_out = wrapper.args[-1]
    try:
        result = body.accept(generator)
        generator.builder.ret(result)
    finally:
        generator.builder, generator.env, generator.refinement_env, generator._filter_length_out = old
