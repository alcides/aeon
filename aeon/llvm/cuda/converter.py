from __future__ import annotations

from typing import List

import llvmlite.binding as llvm
import llvmlite.ir as ir

from aeon.llvm.cpu.converter import CPULLVMIRGenerator
from aeon.llvm.utils import is_array_pointer, sanitize_name
from aeon.llvm.llvm_ast import (
    LLVMFunction,
    LLVMFunctionType,
    LLVMPointerType,
    LLVMVectorMap,
    LLVMVectorReduce,
    LLVMVectorZipWith,
    LLVMType,
    LLVMNDArrayType,
    LLVMNDArrayOp,
    LLVMRefinedValue,
    LLVMVar,
    LLVMLiteral,
)
from aeon.llvm.ndarray import axis_value, element_pointer, emit_row


class CUDALLVMIRGenerator(CPULLVMIRGenerator):
    def __init__(self, use_refinements: bool = True) -> None:
        super().__init__(use_refinements=use_refinements)
        self.module.name = "aeon_cuda_module"
        self.module.triple = "nvptx64-nvidia-cuda"
        self.module.data_layout = (
            "e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-"
            "f32:32:32-f64:64:64-v16:16:16-v32:32:32-v64:64:64-v128:128:128-n32:64"
        )
        llvm.initialize_all_targets()
        target = llvm.Target.from_triple(self.module.triple)
        self.target_data = target.create_target_machine().target_data
        self.kernels: List[ir.Function] = []
        self.ndarray_launches: dict[str, tuple[int, int]] = {}
        self.row_launches: dict[str, int] = {}

    def _get_type_size(self, ir_type: ir.Type) -> int:
        return ir_type.get_abi_size(self.target_data)

    def _get_type_alignment(self, ir_type: ir.Type) -> int:
        return ir_type.get_abi_alignment(self.target_data)

    def visit_var(self, node: LLVMVar) -> ir.Value:
        name = sanitize_name(node.name)
        if name not in self.env and name not in self.module.globals:
            if node.name.name in {"sqrt", "sqrtf", "Math_sqrt", "Math_sqrtf"}:
                # NVPTX has no host libm. LLVM lowers this intrinsic directly to
                # a device square root, without requiring a libdevice link.
                assert isinstance(node.type, LLVMFunctionType)
                return self.module.declare_intrinsic("llvm.sqrt", [self.to_ir_type(node.type.arg_types[0])])
        return super().visit_var(node)

    def _add_kernel_metadata(self, func: ir.Function) -> None:
        nvvm_annot = self.module.add_named_metadata("nvvm.annotations")
        md_node = self.module.add_metadata([func, "kernel", ir.Constant(ir.IntType(32), 1)])  # func, "kernel", i32 1
        nvvm_annot.add(md_node)
        if func not in self.kernels:
            self.kernels.append(func)

    def generate_ir(self, definitions, initial_env=None) -> str:
        super().generate_ir(definitions, initial_env)
        # Device functions (including recursive helpers) must remain callable.
        # CUDA entry points are void wrappers, with a result buffer for scalars.
        for node in definitions:
            if not isinstance(node, LLVMFunction) or node.name is None:
                continue
            func = self.module.globals[sanitize_name(node.name)]
            # Array returns identify an input buffer through a device-pointer
            # result slot. Opaque ADT returns remain device-local.
            if isinstance(func.function_type.return_type, ir.PointerType):
                assert isinstance(node.type, LLVMFunctionType)
                ret_type = node.type.return_type
                if not (is_array_pointer(ret_type) or isinstance(ret_type, LLVMNDArrayType)) or not any(
                    isinstance(arg_type, type(ret_type)) and arg_type.element_type == ret_type.element_type
                    for arg_type in node.arg_types
                ):
                    continue
            name = func.name + "__kernel"
            if name in self.module.globals:
                continue
            returns_value = not isinstance(func.function_type.return_type, ir.VoidType)
            args = list(func.function_type.args)
            if returns_value:
                args.append(ir.PointerType(func.function_type.return_type))
            kernel = ir.Function(self.module, ir.FunctionType(ir.VoidType(), args), name=name)
            for argument in kernel.args:
                self._add_parameter_attributes(argument)
            builder = ir.IRBuilder(kernel.append_basic_block("entry"))
            body = node.body
            while isinstance(body, LLVMRefinedValue):
                body = body.value
            if (
                isinstance(body, LLVMNDArrayOp)
                and body.op == "map_rows"
                and isinstance(body.array, LLVMVar)
                and body.array.name in node.arg_names
            ):
                self.row_launches[func.name] = node.arg_names.index(body.array.name)
                self._parallel_rows_wrapper(node, body, kernel, builder)
            elif (
                isinstance(body, LLVMNDArrayOp)
                and body.op == "fill"
                and isinstance(body.array, LLVMVar)
                and body.array.name in node.arg_names
                and isinstance(body.args[0], (LLVMLiteral, LLVMVar))
            ):
                index = node.arg_names.index(body.array.name)
                assert isinstance(body.array.type, LLVMNDArrayType)
                rank = body.array.type.rank
                self.ndarray_launches[func.name] = (index, rank)
                self._parallel_fill_wrapper(node, body, kernel, builder)
            else:
                result = builder.call(func, list(kernel.args[: len(func.args)]))
                if returns_value:
                    builder.store(result, kernel.args[-1])
                builder.ret_void()
            self._add_kernel_metadata(kernel)
        return str(self.module)

    def _parallel_rows_wrapper(self, node, body, kernel, builder):
        old_builder, old_env = self.builder, self.env
        old_refinements = self.refinement_env
        self.builder = builder
        self.env = {sanitize_name(name): arg for name, arg in zip(node.arg_names, kernel.args)}
        self.refinement_env = dict(zip(node.arg_names, kernel.args))
        array = body.array.accept(self)
        i64 = ir.IntType(64)
        tid, block, threads = [
            builder.zext(builder.call(self._get_cuda_intrinsic(reg), []), i64) for reg in ("tid.x", "ctaid.x", "ntid.x")
        ]
        index = builder.add(tid, builder.mul(block, threads))
        row = builder.alloca(array.type.pointee, name="row_descriptor")
        with builder.if_then(builder.icmp_unsigned("<", index, axis_value(builder, array, 3, 0))):
            emit_row(self, body, array, index, row)
        with builder.if_then(builder.icmp_unsigned("==", index, ir.Constant(i64, 0))):
            builder.store(array, kernel.args[-1])
        builder.ret_void()
        self.builder, self.env = old_builder, old_env
        self.refinement_env = old_refinements

    def _parallel_fill_wrapper(self, node, body, kernel, builder):
        old_builder, old_env = self.builder, self.env
        self.builder = builder
        self.env = {sanitize_name(name): arg for name, arg in zip(node.arg_names, kernel.args)}
        array = body.array.accept(self)
        ty = body.array.type
        value = self._coerce_to_type(body.args[0].accept(self), ty.element_type.to_ir())
        coordinates = []
        for axis in reversed("xyz"[: ty.rank]):

            def intrinsic(reg):
                return builder.zext(builder.call(self._get_cuda_intrinsic(f"{reg}.{axis}"), []), ir.IntType(64))

            coordinates.append(builder.add(intrinsic("tid"), builder.mul(intrinsic("ctaid"), intrinsic("ntid"))))
        valid = ir.Constant(ir.IntType(1), 1)
        first = ir.Constant(ir.IntType(1), 1)
        for axis, coordinate in enumerate(coordinates):
            valid = builder.and_(valid, builder.icmp_unsigned("<", coordinate, axis_value(builder, array, 3, axis)))
            first = builder.and_(first, builder.icmp_unsigned("==", coordinate, ir.Constant(ir.IntType(64), 0)))
        with builder.if_then(valid):
            builder.store(value, element_pointer(builder, array, coordinates))
        with builder.if_then(first):
            builder.store(array, kernel.args[-1])
        builder.ret_void()
        self.builder, self.env = old_builder, old_env

    def _get_cuda_intrinsic(self, name: str) -> ir.Function:
        intrinsic_map = {
            "tid.x": "llvm.nvvm.read.ptx.sreg.tid.x",
            "ntid.x": "llvm.nvvm.read.ptx.sreg.ntid.x",
            "ctaid.x": "llvm.nvvm.read.ptx.sreg.ctaid.x",
            "nctaid.x": "llvm.nvvm.read.ptx.sreg.nctaid.x",
        }
        for axis in "yz":
            for register in ("tid", "ntid", "ctaid", "nctaid"):
                intrinsic_map[f"{register}.{axis}"] = f"llvm.nvvm.read.ptx.sreg.{register}.{axis}"
        llvm_name = intrinsic_map.get(name)
        if not llvm_name:
            raise ValueError(f"unknown CUDA intrinsic {name}")

        if llvm_name in self.module.globals:
            return self.module.globals[llvm_name]

        f_ty = ir.FunctionType(ir.IntType(32), [])
        return ir.Function(self.module, f_ty, name=llvm_name)

    def _get_global_id(self) -> ir.Value:
        tid_x = self.builder.call(self._get_cuda_intrinsic("tid.x"), [])
        ctaid_x = self.builder.call(self._get_cuda_intrinsic("ctaid.x"), [])
        ntid_x = self.builder.call(self._get_cuda_intrinsic("ntid.x"), [])
        return self.builder.add(tid_x, self.builder.mul(ctaid_x, ntid_x))

    def to_ir_type(self, ty: LLVMType) -> ir.Type:
        if isinstance(ty, LLVMPointerType):
            base = self.to_ir_type(ty.element_type)
            if isinstance(base, ir.VoidType):
                base = ir.IntType(8)
            return ir.PointerType(base, ty.address_space.value)
        return super().to_ir_type(ty)

    def _emit_cuda_launch(self, func: ir.Function, args: List[ir.Value], size: ir.Value) -> None:
        block_size = ir.Constant(ir.IntType(32), 256)
        size_32 = self.builder.trunc(size, ir.IntType(32)) if size.type.width > 32 else size
        grid_size = self.builder.sdiv(self.builder.add(size_32, ir.Constant(ir.IntType(32), 255)), block_size)

        arg_types = func.function_type.args
        total_size = 0
        for t in arg_types:
            align = self._get_type_alignment(t)
            total_size = (total_size + align - 1) & ~(align - 1)
            total_size += self._get_type_size(t)

        alignment = 8
        get_buffer_ty = ir.FunctionType(ir.PointerType(ir.IntType(8)), [ir.IntType(64), ir.IntType(64)])
        get_buffer = self.module.globals.get("cudaGetParameterBuffer")
        if not get_buffer:
            get_buffer = ir.Function(self.module, get_buffer_ty, name="cudaGetParameterBuffer")

        buffer = self.builder.call(
            get_buffer, [ir.Constant(ir.IntType(64), alignment), ir.Constant(ir.IntType(64), total_size)]
        )

        offset = 0
        for arg in args:
            align = self._get_type_alignment(arg.type)
            offset = (offset + align - 1) & ~(align - 1)
            arg_ptr = self.builder.gep(buffer, [ir.Constant(ir.IntType(32), offset)])
            cast_ptr = self.builder.bitcast(arg_ptr, ir.PointerType(arg.type))
            self.builder.store(arg, cast_ptr)
            offset += self._get_type_size(arg.type)

        launch_ty = ir.FunctionType(
            ir.IntType(32),
            [
                ir.PointerType(ir.IntType(8)),  # func
                ir.PointerType(ir.IntType(8)),  # buffer
                ir.IntType(32),
                ir.IntType(32),
                ir.IntType(32),  # grid
                ir.IntType(32),
                ir.IntType(32),
                ir.IntType(32),  # block
                ir.IntType(32),  # shared mem
                ir.PointerType(ir.IntType(8)),  # stream
            ],
        )
        launch_func = self.module.globals.get("cudaLaunchDevice")
        if not launch_func:
            launch_func = ir.Function(self.module, launch_ty, name="cudaLaunchDevice")

        func_ptr = self.builder.bitcast(func, ir.PointerType(ir.IntType(8)))
        zero = ir.Constant(ir.IntType(32), 0)
        one = ir.Constant(ir.IntType(32), 1)
        null_stream = ir.Constant(ir.PointerType(ir.IntType(8)), None)

        self.builder.call(launch_func, [func_ptr, buffer, grid_size, one, one, block_size, one, one, zero, null_stream])

    def visit_vector_map(self, node: LLVMVectorMap) -> ir.Value:
        res_ty, f, v, size = node.type, node.f, node.v, node.size
        self._is_top_level = False
        f_val, v_val, size_val = f.accept(self), v.accept(self), size.accept(self)
        res_base_ty = self.to_ir_type(res_ty.element_type if isinstance(res_ty, LLVMPointerType) else res_ty)
        if isinstance(res_base_ty, ir.VoidType):
            res_base_ty = ir.IntType(32)

        kernel_name = f"map_kernel_{self.fn_count}"
        self.fn_count += 1

        v_in_ty = v_val.type
        v_out_ty = ir.PointerType(res_base_ty, 1)
        kernel_ty = ir.FunctionType(ir.VoidType(), [v_in_ty, v_out_ty, ir.IntType(32)])
        kernel_func = ir.Function(self.module, kernel_ty, name=kernel_name)
        self._add_kernel_metadata(kernel_func)

        old_builder = self.builder
        self.builder = ir.IRBuilder(kernel_func.append_basic_block("entry"))
        v_in, v_out, sz = kernel_func.args
        idx = self._get_global_id()
        with self.builder.if_then(self.builder.icmp_signed("<", idx, sz)):
            val = self.builder.load(self.builder.gep(v_in, [idx]))
            mapped_val = self.builder.call(f_val, [val])
            if not isinstance(mapped_val.type, ir.VoidType):
                self.builder.store(mapped_val, self.builder.gep(v_out, [idx]))
        self.builder.ret_void()
        self.builder = old_builder

        new_v = self._heap_alloc(res_base_ty, size_val)
        self._emit_cuda_launch(kernel_func, [v_val, new_v, size_val], size_val)
        return new_v

    def visit_vector_zipwith(self, node: LLVMVectorZipWith) -> ir.Value:
        res_ty, f, v1, v2, size = node.type, node.f, node.v1, node.v2, node.size
        self._is_top_level = False
        f_val, v1_val, v2_val, size_val = f.accept(self), v1.accept(self), v2.accept(self), size.accept(self)
        res_base_ty = self.to_ir_type(res_ty.element_type if isinstance(res_ty, LLVMPointerType) else res_ty)

        kernel_name = f"zip_kernel_{self.fn_count}"
        self.fn_count += 1

        v1_ty, v2_ty = v1_val.type, v2_val.type
        v_out_ty = ir.PointerType(res_base_ty, 1)
        kernel_ty = ir.FunctionType(ir.VoidType(), [v1_ty, v2_ty, v_out_ty, ir.IntType(32)])
        kernel_func = ir.Function(self.module, kernel_ty, name=kernel_name)
        self._add_kernel_metadata(kernel_func)

        old_builder = self.builder
        self.builder = ir.IRBuilder(kernel_func.append_basic_block("entry"))
        v1_arg, v2_arg, v_out_arg, sz_arg = kernel_func.args
        idx = self._get_global_id()
        with self.builder.if_then(self.builder.icmp_signed("<", idx, sz_arg)):
            val1 = self.builder.load(self.builder.gep(v1_arg, [idx]))
            val2 = self.builder.load(self.builder.gep(v2_arg, [idx]))
            res = self.builder.call(f_val, [val1, val2])
            self.builder.store(res, self.builder.gep(v_out_arg, [idx]))
        self.builder.ret_void()
        self.builder = old_builder

        new_v = self._heap_alloc(res_base_ty, size_val)
        self._emit_cuda_launch(kernel_func, [v1_val, v2_val, new_v, size_val], size_val)
        return new_v

    def visit_vector_reduce(self, node: LLVMVectorReduce) -> ir.Value:
        return super().visit_vector_reduce(node)
