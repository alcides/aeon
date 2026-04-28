from __future__ import annotations


import llvmlite.binding as llvm
import llvmlite.ir as ir
from typing import Any, Dict

from aeon.llvm.cpu.converter import CPULLVMIRGenerator
from aeon.llvm.llvm_ast import (
    LLVMFunction,
    LLVMFunctionType,
    LLVMPointerType,
    LLVMVectorMap,
    LLVMVectorIMap,
    LLVMVectorReduce,
    LLVMVectorZipWith,
    LLVMVectorCount,
    LLVMVoidType,
    LLVMVar,
    LLVMTerm,
    LLVMLet,
)
from aeon.llvm.utils import sanitize_name
from aeon.utils.name import Name


class CUDALLVMIRGenerator(CPULLVMIRGenerator):
    def __init__(self) -> None:
        super().__init__()
        self._reset_module()

    def _reset_module(self) -> None:
        self.module = ir.Module(name="aeon_cuda_module")
        self.module.triple = "nvptx64-nvidia-cuda"
        self.module.data_layout = (
            "e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-"
            "f32:32:32-f64:64:64-v16:16:16-v32:32:32-v64:64:64-v128:128:128-n32:64"
        )
        self.kernel_names: set[str] = set()
        self.fn_count = 0
        self.env: dict[str, Any] = {}
        self.ast_env: dict[Name, LLVMTerm] = {}
        self.vector_op_depth = 0
        llvm.initialize_all_targets()

    def generate_ir(self, definitions: list[LLVMTerm], initial_env: Dict[str, Any] = None) -> str:
        self._reset_module()
        if initial_env:
            self.env.update(initial_env)
        kernels: list[LLVMFunction] = [d for d in definitions if isinstance(d, LLVMFunction)]
        for k in kernels:
            self.ast_env[k.name] = k

        all_called = set()

        for k in kernels:
            all_called.update(k.body.find_calls())

        all_called_base_names = {n.name for n in all_called}
        self.kernel_names = {
            sanitize_name(k.name)
            for k in kernels
            if k.name and k.name not in all_called and k.name.name not in all_called_base_names
        }

        all_funcs = []
        for k in kernels:
            self._is_top_level = True
            func = k.accept(self)
            all_funcs.append((k, func))

        for k, func in all_funcs:
            if sanitize_name(k.name) in self.kernel_names:
                self._create_kernel_wrapper(k, func)

        return str(self.module)

    def _create_kernel_wrapper(self, node: LLVMFunction, func: ir.Function) -> None:
        wrapper_name = f"{func.name}_kernel"
        ir_arg_types = [self.to_ir_type(t) for t in node.arg_types]
        assert isinstance(node.type, LLVMFunctionType)
        ret_type = node.type.return_type
        has_scalar_return = not isinstance(ret_type, (LLVMVoidType, LLVMPointerType))
        if has_scalar_return:
            ir_arg_types.append(self.to_ir_type(ret_type).as_pointer())
        f_ty = ir.FunctionType(ir.VoidType(), ir_arg_types)
        wrapper = ir.Function(self.module, f_ty, name=wrapper_name)

        try:
            nvvm_annot = self.module.get_named_metadata("nvvm.annotations")
        except KeyError:
            nvvm_annot = self.module.add_named_metadata("nvvm.annotations")
        md_node = self.module.add_metadata([wrapper, "kernel", ir.Constant(ir.IntType(32), 1)])
        nvvm_annot.add(md_node)

        builder = ir.IRBuilder(wrapper.append_basic_block(name="entry"))
        idx = self._get_cuda_id_in_builder(builder)

        orig_args = list(wrapper.args)
        if has_scalar_return:
            out_ptr = orig_args.pop()

        if has_scalar_return:
            res = builder.call(func, orig_args)
            with builder.if_then(builder.icmp_signed("==", idx, ir.Constant(ir.IntType(32), 0))):
                builder.store(res, out_ptr)
        else:
            size_val = None
            for i, (arg, ty) in enumerate(zip(orig_args, node.arg_types)):
                if i == len(orig_args) - 1 and isinstance(self.to_ir_type(ty), ir.IntType):
                    size_val = arg
            if size_val:
                with builder.if_then(builder.icmp_signed("<", idx, size_val)):
                    builder.call(func, orig_args)
            else:
                builder.call(func, orig_args)
        builder.ret_void()

    def visit_function(self, node: LLVMFunction) -> ir.Function:
        func_name = sanitize_name(node.name) if node.name else f"anon_{self.fn_count}"
        if not node.name:
            self.fn_count += 1
        if func_name in self.module.globals:
            return self.module.globals[func_name]

        assert isinstance(node.type, LLVMFunctionType)
        ret_ty = self.to_ir_type(node.type.return_type)
        if isinstance(node.type.return_type, LLVMFunctionType):
            ret_ty = self.to_ir_type(node.type.return_type).as_pointer()

        f_ty = ir.FunctionType(ret_ty, [self.to_ir_type(t) for t in node.arg_types])
        func = ir.Function(self.module, f_ty, name=func_name)
        func.linkage = "internal"

        old_builder, old_env = self.builder, self.env.copy()
        self.builder = ir.IRBuilder(func.append_basic_block(name="entry"))

        for i, arg_name in enumerate(node.arg_names):
            name = sanitize_name(arg_name)
            func.args[i].name = name
            self.env[name] = func.args[i]

        self._is_top_level = False
        ret_val = node.body.accept(self)

        if not self.builder.block.is_terminated:
            if isinstance(func.function_type.return_type, ir.VoidType):
                self.builder.ret_void()
            else:
                if ret_val is None:
                    ret_val = ir.Constant(func.function_type.return_type, 0)
                self.builder.ret(self._cast_if_needed(ret_val, func.function_type.return_type))

        self.builder, self.env = old_builder, old_env
        return func

    def visit_var(self, node: LLVMVar) -> ir.Value:
        name = sanitize_name(node.name)
        if name in self.env:
            return self.env[name]
        if name in self.module.globals:
            return self.module.globals[name]
        base_name = node.name.name
        if base_name in self.env:
            return self.env[base_name]
        if base_name in self.module.globals:
            return self.module.globals[base_name]
        return super().visit_var(node)

    def _execute_vector_op(self, size_val, body_fn):
        if self.vector_op_depth > 0:
            self.to_ir_loop(size_val, f"nested_{self.vector_op_depth}", body_fn)
        else:
            self.vector_op_depth += 1
            idx = self._get_global_id()
            with self.builder.if_then(self.builder.icmp_signed("<", idx, size_val)):
                body_fn(idx)
            self.vector_op_depth -= 1

    def _resolve_actual_f(self, f_node: LLVMTerm) -> LLVMTerm:
        if isinstance(f_node, LLVMVar):
            if f_node.name in self.ast_env:
                return self.ast_env[f_node.name]
            for key, val in self.ast_env.items():
                if key.name == f_node.name.name:
                    return val
        return f_node

    def _inline_or_call(self, f_node: LLVMTerm, args: list[ir.Value]) -> ir.Value:
        actual_f = self._resolve_actual_f(f_node)
        if isinstance(actual_f, LLVMFunction):
            old_env = self.env.copy()
            for name, val in zip(actual_f.arg_names, args):
                self.env[sanitize_name(name)] = val
            res = actual_f.body.accept(self)
            self.env = old_env
            return res

        target_func = f_node.accept(self)
        if isinstance(target_func, ir.Function):
            new_arg_vals = []
            for arg_val, expected_ty in zip(args, target_func.function_type.args):
                new_arg_vals.append(self._cast_if_needed(arg_val, expected_ty))
            args = new_arg_vals
        return self.builder.call(target_func, args)

    def visit_vector_map(self, node: LLVMVectorMap) -> ir.Value:
        v_val, size_val = node.v.accept(self), node.size.accept(self)

        def body(idx):
            self._is_top_level = False
            ptr = self.builder.gep(v_val, [idx])
            val = self.builder.load(ptr)
            res = self._inline_or_call(node.f, [val])
            if res is not None and not isinstance(res.type, ir.VoidType):
                self.builder.store(self._cast_if_needed(res, ptr.type.pointee), ptr)

        self._execute_vector_op(size_val, body)
        return v_val

    def visit_vector_imap(self, node: LLVMVectorIMap) -> ir.Value:
        v_val, size_val = node.v.accept(self), node.size.accept(self)

        def body(idx):
            self._is_top_level = False
            ptr = self.builder.gep(v_val, [idx])
            val = self.builder.load(ptr)
            res = self._inline_or_call(node.f, [idx, val])
            if res is not None and not isinstance(res.type, ir.VoidType):
                self.builder.store(self._cast_if_needed(res, ptr.type.pointee), ptr)

        self._execute_vector_op(size_val, body)
        return v_val

    def visit_vector_zipwith(self, node: LLVMVectorZipWith) -> ir.Value:
        v1, v2, size = node.v1.accept(self), node.v2.accept(self), node.size.accept(self)

        def body(idx):
            self._is_top_level = False
            ptr = self.builder.gep(v1, [idx])
            v1_val, v2_val = self.builder.load(ptr), self.builder.load(self.builder.gep(v2, [idx]))
            res = self._inline_or_call(node.f, [v1_val, v2_val])
            if res is not None and not isinstance(res.type, ir.VoidType):
                self.builder.store(self._cast_if_needed(res, ptr.type.pointee), ptr)

        self._execute_vector_op(size, body)
        return v1

    def visit_vector_count(self, node: LLVMVectorCount) -> ir.Value:
        v_val, size_val = node.v.accept(self), node.size.accept(self)

        if self.vector_op_depth > 0:
            count_ptr = self.builder.alloca(ir.IntType(32), name="count_res")
            self.builder.store(ir.Constant(ir.IntType(32), 0), count_ptr)

            def body(idx):
                self._is_top_level = False
                val = self.builder.load(self.builder.gep(v_val, [idx]))
                is_match = self._inline_or_call(node.f, [val])
                with self.builder.if_then(self._cast_if_needed(is_match, ir.IntType(1))):
                    curr = self.builder.load(count_ptr)
                    self.builder.store(self.builder.add(curr, ir.Constant(ir.IntType(32), 1)), count_ptr)

            self.to_ir_loop(size_val, "count", body)
            return self.builder.load(count_ptr)
        else:
            self.vector_op_depth += 1
            idx = self._get_global_id()
            res_ptr = self.builder.alloca(ir.IntType(32), name="global_count_res")
            self.builder.store(ir.Constant(ir.IntType(32), 0), res_ptr)
            with self.builder.if_then(self.builder.icmp_signed("==", idx, ir.Constant(ir.IntType(32), 0))):

                def body(i):
                    self._is_top_level = False
                    val = self.builder.load(self.builder.gep(v_val, [i]))
                    is_match = self._inline_or_call(node.f, [val])
                    with self.builder.if_then(self._cast_if_needed(is_match, ir.IntType(1))):
                        curr = self.builder.load(res_ptr)
                        self.builder.store(self.builder.add(curr, ir.Constant(ir.IntType(32), 1)), res_ptr)

                self.to_ir_loop(size_val, "global_count", body)
            self.vector_op_depth -= 1
            return self.builder.load(res_ptr)

    def visit_let(self, node: LLVMLet) -> ir.Value | None:
        if isinstance(node.var_value, LLVMFunction):
            self.ast_env[node.var_name] = node.var_value
            return node.body.accept(self)
        return super().visit_let(node)

    def _get_cuda_intrinsic_in_builder(self, builder: ir.IRBuilder, name: str) -> ir.Function:
        intrinsic_map = {
            "tid.x": "llvm.nvvm.read.ptx.sreg.tid.x",
            "ntid.x": "llvm.nvvm.read.ptx.sreg.ntid.x",
            "ctaid.x": "llvm.nvvm.read.ptx.sreg.ctaid.x",
        }
        llvm_name = intrinsic_map.get(name)
        if llvm_name in self.module.globals:
            return self.module.globals[llvm_name]
        return ir.Function(self.module, ir.FunctionType(ir.IntType(32), []), name=llvm_name)

    def _get_cuda_id_in_builder(self, builder: ir.IRBuilder) -> ir.Value:
        t, c, n = [
            builder.call(self._get_cuda_intrinsic_in_builder(builder, i), []) for i in ["tid.x", "ctaid.x", "ntid.x"]
        ]
        return builder.add(t, builder.mul(c, n))

    def _get_global_id(self) -> ir.Value:
        return self._get_cuda_id_in_builder(self.builder)

    def visit_vector_reduce(self, node: LLVMVectorReduce) -> ir.Value:
        return super().visit_vector_reduce(node)
