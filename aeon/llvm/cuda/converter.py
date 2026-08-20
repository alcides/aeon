from __future__ import annotations


import llvmlite.binding as llvm
import llvmlite.ir as ir
from typing import Any, Callable

from aeon.llvm.cpu.converter import CPULLVMIRGenerator, VectorExecutor, LLVMIRGenerationError
from aeon.llvm.cuda.plan import (
    CudaCommonKernelName,
    CudaKernelPlan,
    CudaKernelPlanner,
    CudaPlanAlgorithm,
    count_map_kernel_name,
    filter_mask_kernel_name,
    filter_scatter_kernel_name,
    reduce_copy_kernel_name,
    reduce_finish_kernel_name,
    reduce_step_kernel_name,
)
from aeon.llvm.llvm_ast import (
    LLVMFunction,
    LLVMFunctionType,
    LLVMPointerType,
    LLVMVectorMap,
    LLVMVectorIMap,
    LLVMVectorReduce,
    LLVMVectorZipWith,
    LLVMVectorFilter,
    LLVMVectorCount,
    LLVMVoidType,
    LLVMVar,
    LLVMTerm,
    LLVMLet,
    LLVMVectorSize,
    LLVMCast,
)
from aeon.llvm.utils import sanitize_name
from aeon.utils.name import Name


class CUDAVectorExecutor(VectorExecutor):
    def execute(self, size_val: ir.Value, name: str, body_fn: Callable[[ir.Value], None]):
        if self.gen.vector_op_depth > 0:
            self.gen.to_ir_loop(size_val, f"nested_{self.gen.vector_op_depth}", body_fn)
        else:
            self.gen.vector_op_depth += 1
            idx = self.gen._get_global_id()
            with self.gen.builder.if_then(self.gen.builder.icmp_signed("<", idx, size_val)):
                body_fn(idx)
            self.gen.vector_op_depth -= 1


class CUDALLVMIRGenerator(CPULLVMIRGenerator):
    def __init__(self) -> None:
        super().__init__()
        self._reset_module()
        self.vector_executor = CUDAVectorExecutor(self)

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
        self.ast_env: dict[str, LLVMTerm] = {}
        self.vector_op_depth = 0
        self._vector_term_bindings: dict[str, LLVMTerm] = {}
        self.kernel_plans: dict[str, CudaKernelPlan] = {}
        llvm.initialize_all_targets()

    def _temp_alloc(self, element_ty: ir.Type, count: ir.Value) -> ir.Value:
        if not isinstance(count, ir.Constant) or int(count.constant) != 1:
            raise LLVMIRGenerationError("device vector temp allocation is disabled")
        return self.builder.alloca(element_ty, count, name="tmp_vec")

    def generate_ir(self, definitions: list[LLVMTerm], initial_env: dict[str, Any] | None = None) -> str:
        self._reset_module()
        self.kernel_plans = CudaKernelPlanner().build(definitions)
        if initial_env:
            self.env.update(initial_env)
        kernels: list[LLVMFunction] = [d for d in definitions if isinstance(d, LLVMFunction)]
        for k in kernels:
            self.ast_env[sanitize_name(k.name)] = k

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
                self._create_planned_count_kernels(k)
                self._create_planned_reduce_kernels(k)
                self._create_planned_filter_kernels(k)

        self._create_common_tree_reduce_kernels()
        self._create_common_scan_kernels()

        return str(self.module)

    def _annotate_kernel(self, func: ir.Function) -> None:
        try:
            nvvm_annot = self.module.get_named_metadata("nvvm.annotations")
        except KeyError:
            nvvm_annot = self.module.add_named_metadata("nvvm.annotations")
        md_node = self.module.add_metadata([func, "kernel", ir.Constant(ir.IntType(32), 1)])
        nvvm_annot.add(md_node)

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

        self._annotate_kernel(wrapper)

        builder = ir.IRBuilder(wrapper.append_basic_block(name="entry"))
        idx = self._get_cuda_id_in_builder(builder)

        orig_args = list(wrapper.args)
        if has_scalar_return:
            out_ptr = orig_args.pop()

        if has_scalar_return:
            with builder.if_then(builder.icmp_signed("==", idx, ir.Constant(ir.IntType(32), 0))):
                res = builder.call(func, orig_args)
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

    def _find_count_with_bindings(
        self, term: LLVMTerm, bindings: dict[str, LLVMTerm] | None = None
    ) -> tuple[LLVMVectorCount, dict[str, LLVMTerm]] | None:
        bindings = dict(bindings or {})
        if isinstance(term, LLVMVectorCount):
            return term, bindings
        if isinstance(term, LLVMLet):
            name = sanitize_name(term.var_name)
            next_bindings = dict(bindings)
            next_bindings[name] = term.var_value
            return self._find_count_with_bindings(term.body, next_bindings) or self._find_count_with_bindings(
                term.var_value, bindings
            )
        if isinstance(term, LLVMCast):
            return self._find_count_with_bindings(term.val, bindings)
        return None

    def _resolve_bound_vector_term(self, term: LLVMTerm, bindings: dict[str, LLVMTerm]) -> LLVMTerm:
        if isinstance(term, LLVMVar):
            return bindings.get(sanitize_name(term.name), term)
        if isinstance(term, LLVMCast):
            return self._resolve_bound_vector_term(term.val, bindings)
        return term

    def _create_planned_count_kernels(self, node: LLVMFunction) -> None:
        if not node.name:
            return
        fn_name = sanitize_name(node.name)
        plan = self.kernel_plans.get(fn_name)
        if plan is None or plan.algorithm != CudaPlanAlgorithm.COUNT_TREE_I32:
            return
        found = self._find_count_with_bindings(node.body)
        if found is None:
            return
        count_node, bindings = found
        source_term = self._resolve_bound_vector_term(count_node.v, bindings)
        map_name = count_map_kernel_name(fn_name)
        if map_name in self.module.globals:
            return

        f_ty = ir.FunctionType(
            ir.VoidType(),
            [self.to_ir_type(t) for t in node.arg_types] + [ir.PointerType(ir.IntType(32))],
        )
        kernel = ir.Function(self.module, f_ty, name=map_name)
        self._annotate_kernel(kernel)

        with self._push_scope():
            self.builder = ir.IRBuilder(kernel.append_basic_block("entry"))
            self.env[fn_name] = kernel
            for i, arg_name in enumerate(node.arg_names):
                arg = kernel.args[i]
                arg.name = sanitize_name(arg_name)
                self.env[arg.name] = arg
            flags_arg = kernel.args[-1]
            flags_arg.name = "count_flags"

            idx = self._get_global_id()
            size_val = kernel.args[len(node.arg_types) - 1]
            with self.builder.if_then(self.builder.icmp_signed("<", idx, size_val)):
                if isinstance(source_term, LLVMVectorZipWith):
                    v1_val = source_term.v1.accept(self)
                    v2_val = source_term.v2.accept(self)
                    left = self.builder.load(self.builder.gep(v1_val, [idx]))
                    right = self.builder.load(self.builder.gep(v2_val, [idx]))
                    value = self._inline_or_call(source_term.f, [left, right])
                else:
                    v_val = source_term.accept(self)
                    value = self.builder.load(self.builder.gep(v_val, [idx]))

                keep = self._inline_or_call(count_node.f, [value])
                flag = self.builder.select(
                    self._cast_if_needed(keep, ir.IntType(1)),
                    ir.Constant(ir.IntType(32), 1),
                    ir.Constant(ir.IntType(32), 0),
                )
                self.builder.store(flag, self.builder.gep(flags_arg, [idx]))

            self.builder.ret_void()

    def _find_reduce_with_bindings(
        self, term: LLVMTerm, bindings: dict[str, LLVMTerm] | None = None
    ) -> tuple[LLVMVectorReduce, dict[str, LLVMTerm]] | None:
        bindings = dict(bindings or {})
        if isinstance(term, LLVMVectorReduce):
            return term, bindings
        if isinstance(term, LLVMLet):
            name = sanitize_name(term.var_name)
            next_bindings = dict(bindings)
            next_bindings[name] = term.var_value
            return self._find_reduce_with_bindings(term.body, next_bindings) or self._find_reduce_with_bindings(
                term.var_value, bindings
            )
        if isinstance(term, LLVMCast):
            return self._find_reduce_with_bindings(term.val, bindings)
        return None

    def _create_planned_reduce_kernels(self, node: LLVMFunction) -> None:
        if not node.name:
            return
        fn_name = sanitize_name(node.name)
        plan = self.kernel_plans.get(fn_name)
        if plan is None or plan.algorithm != CudaPlanAlgorithm.REDUCE_TREE:
            return
        found = self._find_reduce_with_bindings(node.body)
        if found is None:
            return
        reduce_node, bindings = found
        source_term = self._resolve_bound_vector_term(reduce_node.v, bindings)
        acc_ty = self.to_ir_type(
            reduce_node.type.element_type if isinstance(reduce_node.type, LLVMPointerType) else reduce_node.type
        )
        if isinstance(acc_ty, ir.VoidType):
            acc_ty = ir.IntType(32)

        copy_name = reduce_copy_kernel_name(fn_name)
        if copy_name not in self.module.globals:
            f_ty = ir.FunctionType(
                ir.VoidType(), [self.to_ir_type(t) for t in node.arg_types] + [ir.PointerType(acc_ty)]
            )
            kernel = ir.Function(self.module, f_ty, name=copy_name)
            self._annotate_kernel(kernel)
            with self._push_scope():
                self.builder = ir.IRBuilder(kernel.append_basic_block("entry"))
                for i, arg_name in enumerate(node.arg_names):
                    arg = kernel.args[i]
                    arg.name = sanitize_name(arg_name)
                    self.env[arg.name] = arg
                work_arg = kernel.args[-1]
                work_arg.name = "reduce_work"
                idx = self._get_global_id()
                size_val = reduce_node.size.accept(self)
                with self.builder.if_then(self.builder.icmp_signed("<", idx, size_val)):
                    v_val = source_term.accept(self)
                    src = self.builder.load(self.builder.gep(v_val, [idx]))
                    self.builder.store(self._cast_if_needed(src, acc_ty), self.builder.gep(work_arg, [idx]))
                self.builder.ret_void()

        step_name = reduce_step_kernel_name(fn_name)
        if step_name not in self.module.globals:
            f_ty = ir.FunctionType(ir.VoidType(), [ir.PointerType(acc_ty), ir.PointerType(acc_ty), ir.IntType(32)])
            kernel = ir.Function(self.module, f_ty, name=step_name)
            self._annotate_kernel(kernel)
            with self._push_scope():
                self.builder = ir.IRBuilder(kernel.append_basic_block("entry"))
                src_arg, dst_arg, n_arg = kernel.args
                idx = self._get_global_id()
                out_n = self.builder.udiv(
                    self.builder.add(n_arg, ir.Constant(ir.IntType(32), 1)), ir.Constant(ir.IntType(32), 2)
                )
                with self.builder.if_then(self.builder.icmp_signed("<", idx, out_n)):
                    left_idx = self.builder.mul(idx, ir.Constant(ir.IntType(32), 2))
                    right_idx = self.builder.add(left_idx, ir.Constant(ir.IntType(32), 1))
                    left = self.builder.load(self.builder.gep(src_arg, [left_idx]))
                    acc_ptr = self.builder.alloca(acc_ty, name="reduce_pair_acc")
                    self.builder.store(left, acc_ptr)
                    with self.builder.if_then(self.builder.icmp_signed("<", right_idx, n_arg)):
                        right = self.builder.load(self.builder.gep(src_arg, [right_idx]))
                        reduced = self._inline_or_call(reduce_node.f, [self.builder.load(acc_ptr), right])
                        self.builder.store(self._cast_if_needed(reduced, acc_ty), acc_ptr)
                    self.builder.store(self.builder.load(acc_ptr), self.builder.gep(dst_arg, [idx]))
                self.builder.ret_void()

        finish_name = reduce_finish_kernel_name(fn_name)
        if finish_name not in self.module.globals:
            f_ty = ir.FunctionType(
                ir.VoidType(),
                [self.to_ir_type(t) for t in node.arg_types] + [ir.PointerType(acc_ty), ir.PointerType(acc_ty)],
            )
            kernel = ir.Function(self.module, f_ty, name=finish_name)
            self._annotate_kernel(kernel)
            with self._push_scope():
                self.builder = ir.IRBuilder(kernel.append_basic_block("entry"))
                for i, arg_name in enumerate(node.arg_names):
                    arg = kernel.args[i]
                    arg.name = sanitize_name(arg_name)
                    self.env[arg.name] = arg
                src_arg = kernel.args[-2]
                out_arg = kernel.args[-1]
                idx = self._get_global_id()
                size_val = reduce_node.size.accept(self)
                init_val = reduce_node.initial.accept(self)
                with self.builder.if_then(self.builder.icmp_signed("==", idx, ir.Constant(ir.IntType(32), 0))):
                    acc_ptr = self.builder.alloca(acc_ty, name="reduce_final_acc")
                    self.builder.store(self._cast_if_needed(init_val, acc_ty), acc_ptr)
                    with self.builder.if_then(self.builder.icmp_signed(">", size_val, ir.Constant(ir.IntType(32), 0))):
                        tree_val = self.builder.load(self.builder.gep(src_arg, [ir.Constant(ir.IntType(32), 0)]))
                        final_val = self._inline_or_call(reduce_node.f, [self.builder.load(acc_ptr), tree_val])
                        self.builder.store(self._cast_if_needed(final_val, acc_ty), acc_ptr)
                    self.builder.store(
                        self.builder.load(acc_ptr), self.builder.gep(out_arg, [ir.Constant(ir.IntType(32), 0)])
                    )
                self.builder.ret_void()

    def _find_filter_with_bindings(
        self, term: LLVMTerm, bindings: dict[str, LLVMTerm] | None = None
    ) -> tuple[LLVMVectorFilter, dict[str, LLVMTerm]] | None:
        bindings = dict(bindings or {})
        if isinstance(term, LLVMVectorFilter):
            return term, bindings
        if isinstance(term, LLVMLet):
            name = sanitize_name(term.var_name)
            next_bindings = dict(bindings)
            next_bindings[name] = term.var_value
            return self._find_filter_with_bindings(term.body, next_bindings) or self._find_filter_with_bindings(
                term.var_value, bindings
            )
        if isinstance(term, LLVMCast):
            return self._find_filter_with_bindings(term.val, bindings)
        return None

    def _create_planned_filter_kernels(self, node: LLVMFunction) -> None:
        if not node.name:
            return
        fn_name = sanitize_name(node.name)
        plan = self.kernel_plans.get(fn_name)
        if plan is None or plan.algorithm not in {
            CudaPlanAlgorithm.FILTER_COMPACT,
            CudaPlanAlgorithm.FILTER_SIZE_SCAN,
        }:
            return
        found = self._find_filter_with_bindings(node.body)
        if found is None:
            return
        filter_node, bindings = found
        source_term = self._resolve_bound_vector_term(filter_node.v, bindings)
        out_ty = self.to_ir_type(
            filter_node.type.element_type if isinstance(filter_node.type, LLVMPointerType) else filter_node.type
        )
        if isinstance(out_ty, ir.VoidType):
            out_ty = ir.IntType(32)

        mask_name = filter_mask_kernel_name(fn_name)
        if mask_name not in self.module.globals:
            f_ty = ir.FunctionType(
                ir.VoidType(),
                [self.to_ir_type(t) for t in node.arg_types] + [ir.PointerType(ir.IntType(32))],
            )
            kernel = ir.Function(self.module, f_ty, name=mask_name)
            self._annotate_kernel(kernel)
            with self._push_scope():
                self.builder = ir.IRBuilder(kernel.append_basic_block("entry"))
                for i, arg_name in enumerate(node.arg_names):
                    arg = kernel.args[i]
                    arg.name = sanitize_name(arg_name)
                    self.env[arg.name] = arg
                mask_arg = kernel.args[-1]
                idx = self._get_global_id()
                size_val = filter_node.size.accept(self)
                with self.builder.if_then(self.builder.icmp_signed("<", idx, size_val)):
                    v_val = source_term.accept(self)
                    val = self.builder.load(self.builder.gep(v_val, [idx]))
                    keep = self._inline_or_call(filter_node.f, [val])
                    mask = self.builder.select(
                        self._cast_if_needed(keep, ir.IntType(1)),
                        ir.Constant(ir.IntType(32), 1),
                        ir.Constant(ir.IntType(32), 0),
                    )
                    self.builder.store(mask, self.builder.gep(mask_arg, [idx]))
                self.builder.ret_void()

        if plan.algorithm == CudaPlanAlgorithm.FILTER_SIZE_SCAN:
            return

        scatter_name = filter_scatter_kernel_name(fn_name)
        if scatter_name not in self.module.globals:
            f_ty = ir.FunctionType(
                ir.VoidType(),
                [self.to_ir_type(t) for t in node.arg_types]
                + [ir.PointerType(ir.IntType(32)), ir.PointerType(ir.IntType(32)), ir.PointerType(out_ty)],
            )
            kernel = ir.Function(self.module, f_ty, name=scatter_name)
            self._annotate_kernel(kernel)
            with self._push_scope():
                self.builder = ir.IRBuilder(kernel.append_basic_block("entry"))
                for i, arg_name in enumerate(node.arg_names):
                    arg = kernel.args[i]
                    arg.name = sanitize_name(arg_name)
                    self.env[arg.name] = arg
                scan_arg = kernel.args[-3]
                mask_arg = kernel.args[-2]
                out_arg = kernel.args[-1]
                idx = self._get_global_id()
                size_val = filter_node.size.accept(self)
                with self.builder.if_then(self.builder.icmp_signed("<", idx, size_val)):
                    mask = self.builder.load(self.builder.gep(mask_arg, [idx]))
                    with self.builder.if_then(self.builder.icmp_signed("!=", mask, ir.Constant(ir.IntType(32), 0))):
                        v_val = source_term.accept(self)
                        val = self.builder.load(self.builder.gep(v_val, [idx]))
                        inclusive_pos = self.builder.load(self.builder.gep(scan_arg, [idx]))
                        out_idx = self.builder.sub(inclusive_pos, ir.Constant(ir.IntType(32), 1))
                        self.builder.store(self._cast_if_needed(val, out_ty), self.builder.gep(out_arg, [out_idx]))
                self.builder.ret_void()

    def _create_common_tree_reduce_kernels(self) -> None:
        i32 = ir.IntType(32)
        if CudaCommonKernelName.REDUCE_I32_STEP.value not in self.module.globals:
            f_ty = ir.FunctionType(ir.VoidType(), [ir.PointerType(i32), ir.PointerType(i32), i32])
            kernel = ir.Function(self.module, f_ty, name=CudaCommonKernelName.REDUCE_I32_STEP.value)
            self._annotate_kernel(kernel)
            builder = ir.IRBuilder(kernel.append_basic_block("entry"))
            src, dst, n = kernel.args
            idx = self._get_cuda_id_in_builder(builder)
            out_n = builder.udiv(builder.add(n, ir.Constant(i32, 1)), ir.Constant(i32, 2))
            with builder.if_then(builder.icmp_signed("<", idx, out_n)):
                left_idx = builder.mul(idx, ir.Constant(i32, 2))
                right_idx = builder.add(left_idx, ir.Constant(i32, 1))
                acc_ptr = builder.alloca(i32, name="reduce_pair_acc")
                builder.store(builder.load(builder.gep(src, [left_idx])), acc_ptr)
                has_right = builder.icmp_signed("<", right_idx, n)
                with builder.if_then(has_right):
                    right = builder.load(builder.gep(src, [right_idx]))
                    builder.store(builder.add(builder.load(acc_ptr), right), acc_ptr)
                builder.store(builder.load(acc_ptr), builder.gep(dst, [idx]))
            builder.ret_void()

        if CudaCommonKernelName.STORE_I32_RESULT.value not in self.module.globals:
            f_ty = ir.FunctionType(ir.VoidType(), [ir.PointerType(i32), ir.PointerType(i32)])
            kernel = ir.Function(self.module, f_ty, name=CudaCommonKernelName.STORE_I32_RESULT.value)
            self._annotate_kernel(kernel)
            builder = ir.IRBuilder(kernel.append_basic_block("entry"))
            src, out = kernel.args
            idx = self._get_cuda_id_in_builder(builder)
            with builder.if_then(builder.icmp_signed("==", idx, ir.Constant(i32, 0))):
                builder.store(builder.load(builder.gep(src, [ir.Constant(i32, 0)])), out)
            builder.ret_void()

        if CudaCommonKernelName.STORE_I32_LAST.value not in self.module.globals:
            f_ty = ir.FunctionType(ir.VoidType(), [ir.PointerType(i32), ir.PointerType(i32), i32])
            kernel = ir.Function(self.module, f_ty, name=CudaCommonKernelName.STORE_I32_LAST.value)
            self._annotate_kernel(kernel)
            builder = ir.IRBuilder(kernel.append_basic_block("entry"))
            src, out, n = kernel.args
            idx = self._get_cuda_id_in_builder(builder)
            with builder.if_then(builder.icmp_signed("==", idx, ir.Constant(i32, 0))):
                with builder.if_else(builder.icmp_signed(">", n, ir.Constant(i32, 0))) as (nonempty, empty):
                    with nonempty:
                        last_idx = builder.sub(n, ir.Constant(i32, 1))
                        builder.store(builder.load(builder.gep(src, [last_idx])), out)
                    with empty:
                        builder.store(ir.Constant(i32, 0), out)
            builder.ret_void()

    def _create_common_scan_kernels(self) -> None:
        i32 = ir.IntType(32)
        if CudaCommonKernelName.SCAN_I32_INCLUSIVE_STEP.value in self.module.globals:
            return
        f_ty = ir.FunctionType(ir.VoidType(), [ir.PointerType(i32), ir.PointerType(i32), i32, i32])
        kernel = ir.Function(self.module, f_ty, name=CudaCommonKernelName.SCAN_I32_INCLUSIVE_STEP.value)
        self._annotate_kernel(kernel)
        builder = ir.IRBuilder(kernel.append_basic_block("entry"))
        src, dst, n, offset = kernel.args
        idx = self._get_cuda_id_in_builder(builder)
        with builder.if_then(builder.icmp_signed("<", idx, n)):
            val_ptr = builder.alloca(i32, name="scan_step_val")
            builder.store(builder.load(builder.gep(src, [idx])), val_ptr)
            with builder.if_then(builder.icmp_signed(">=", idx, offset)):
                prev_idx = builder.sub(idx, offset)
                builder.store(builder.add(builder.load(val_ptr), builder.load(builder.gep(src, [prev_idx]))), val_ptr)
            builder.store(builder.load(val_ptr), builder.gep(dst, [idx]))
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

        with self._push_scope():
            self.env[func_name] = func
            self.builder = ir.IRBuilder(func.append_basic_block(name="entry"))

            for i, arg_name in enumerate(node.arg_names):
                name = sanitize_name(arg_name)
                func.args[i].name = name
                self.env[name] = func.args[i]

            self._is_top_level = False
            plan = self.kernel_plans.get(func_name)
            if plan is not None and plan.algorithm in {
                CudaPlanAlgorithm.REDUCE_TREE,
                CudaPlanAlgorithm.FILTER_COMPACT,
                CudaPlanAlgorithm.FILTER_SIZE_SCAN,
            }:
                if isinstance(func.function_type.return_type, ir.PointerType):
                    ret_val = ir.Constant(func.function_type.return_type, None)
                elif isinstance(func.function_type.return_type, ir.VoidType):
                    ret_val = None
                else:
                    ret_val = ir.Constant(func.function_type.return_type, 0)
            else:
                force_loop_mode = not isinstance(node.type.return_type, (LLVMVoidType, LLVMPointerType))
                if force_loop_mode:
                    self.vector_op_depth += 1
                try:
                    ret_val = node.body.accept(self)
                finally:
                    if force_loop_mode:
                        self.vector_op_depth -= 1

            if not self.builder.block.is_terminated:
                if isinstance(func.function_type.return_type, ir.VoidType):
                    self.builder.ret_void()
                else:
                    if ret_val is None:
                        ret_val = ir.Constant(func.function_type.return_type, 0)
                    self.builder.ret(self._cast_if_needed(ret_val, func.function_type.return_type))

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

    def _resolve_actual_f(self, f_node: LLVMTerm) -> LLVMTerm:
        if isinstance(f_node, LLVMVar):
            name = sanitize_name(f_node.name)
            if name in self.ast_env:
                return self.ast_env[name]
            for key, val in self.ast_env.items():
                if key == f_node.name.name:
                    return val
        return f_node

    def _inline_or_call(self, f_node: LLVMTerm, args: list[ir.Value]) -> ir.Value:
        if isinstance(f_node, LLVMVar):
            func_name = sanitize_name(f_node.name)
            target = self.env.get(func_name) or self.module.globals.get(func_name)
            if isinstance(target, ir.Function):
                cast_args = [self._cast_if_needed(arg, ty) for arg, ty in zip(args, target.function_type.args)]
                return self.builder.call(target, cast_args)

        actual_f = self._resolve_actual_f(f_node)
        if isinstance(actual_f, LLVMFunction):
            with self._push_scope():
                for name, declared_ty, val in zip(actual_f.arg_names, actual_f.arg_types, args):
                    self.env[sanitize_name(name)] = self._cast_if_needed(val, self.to_ir_type(declared_ty))
                return actual_f.body.accept(self)

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

        self.vector_executor.execute(size_val, "vector_map", body)
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

        self.vector_executor.execute(size_val, "vector_imap", body)
        return v_val

    def visit_vector_zipwith(self, node: LLVMVectorZipWith) -> ir.Value:
        v1, v2, size = node.v1.accept(self), node.v2.accept(self), node.size.accept(self)
        if isinstance(v1.type, ir.PointerType):
            in_ty = v1.type.pointee
            out_ty = self.to_ir_type(node.type.element_type if isinstance(node.type, LLVMPointerType) else node.type)
            if in_ty != out_ty:
                raise LLVMIRGenerationError("type-changing CUDA zipWith is unsupported")
        out_v = v1

        def body(idx):
            self._is_top_level = False
            v1_val = self.builder.load(self.builder.gep(v1, [idx]))
            v2_val = self.builder.load(self.builder.gep(v2, [idx]))
            res = self._inline_or_call(node.f, [v1_val, v2_val])
            if res is not None and not isinstance(res.type, ir.VoidType):
                out_ptr = self.builder.gep(out_v, [idx])
                self.builder.store(self._cast_if_needed(res, out_ptr.type.pointee), out_ptr)

        self.vector_executor.execute(size, "vector_zipwith", body)
        return out_v

    def visit_vector_count(self, node: LLVMVectorCount) -> ir.Value:
        size_val = node.size.accept(self)

        zip_node: LLVMVectorZipWith | None = None
        if isinstance(node.v, LLVMVectorZipWith):
            zip_node = node.v
        elif isinstance(node.v, LLVMCast) and isinstance(node.v.val, LLVMVectorZipWith):
            zip_node = node.v.val
        elif isinstance(node.v, LLVMVar):
            bound = self._vector_term_bindings.get(sanitize_name(node.v.name))
            if isinstance(bound, LLVMVectorZipWith):
                zip_node = bound
            elif isinstance(bound, LLVMCast) and isinstance(bound.val, LLVMVectorZipWith):
                zip_node = bound.val

        if zip_node is not None:
            v1_val = zip_node.v1.accept(self)
            v2_val = zip_node.v2.accept(self)

            count_ptr = self.builder.alloca(ir.IntType(32), name="count_res")
            self.builder.store(ir.Constant(ir.IntType(32), 0), count_ptr)

            def body(idx):
                self._is_top_level = False
                v1_elem = self.builder.load(self.builder.gep(v1_val, [idx]))
                v2_elem = self.builder.load(self.builder.gep(v2_val, [idx]))
                zipped = self._inline_or_call(zip_node.f, [v1_elem, v2_elem])
                is_match = self._inline_or_call(node.f, [zipped])
                with self.builder.if_then(self._cast_if_needed(is_match, ir.IntType(1))):
                    curr = self.builder.load(count_ptr)
                    self.builder.store(self.builder.add(curr, ir.Constant(ir.IntType(32), 1)), count_ptr)

            self.to_ir_loop(size_val, "count_zipwith_fused", body)
            return self.builder.load(count_ptr)

        v_val = node.v.accept(self)

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
            self.ast_env[sanitize_name(node.var_name)] = node.var_value
            return node.body.accept(self)

        def uses_fused_count_var(term: LLVMTerm, var_name: str) -> bool:
            if isinstance(term, LLVMVectorCount):
                body_v = term.v
                if isinstance(body_v, LLVMVar):
                    return sanitize_name(body_v.name) == var_name
                if isinstance(body_v, LLVMCast) and isinstance(body_v.val, LLVMVar):
                    return sanitize_name(body_v.val.name) == var_name
                return False
            if isinstance(term, LLVMLet):
                return uses_fused_count_var(term.var_value, var_name) or uses_fused_count_var(term.body, var_name)
            if isinstance(term, LLVMCast):
                return uses_fused_count_var(term.val, var_name)
            return False

        def uses_filter_size_var(term: LLVMTerm, var_name: str) -> bool:
            if isinstance(term, LLVMVectorSize):
                body_v = term.v
                if isinstance(body_v, LLVMVar):
                    return sanitize_name(body_v.name) == var_name
                if isinstance(body_v, LLVMCast) and isinstance(body_v.val, LLVMVar):
                    return sanitize_name(body_v.val.name) == var_name
                return False
            if isinstance(term, LLVMLet):
                return uses_filter_size_var(term.var_value, var_name) or uses_filter_size_var(term.body, var_name)
            if isinstance(term, LLVMCast):
                return uses_filter_size_var(term.val, var_name)
            return False

        binding_name = sanitize_name(node.var_name)
        if isinstance(node.var_value, LLVMVectorZipWith) and uses_fused_count_var(node.body, binding_name):
            previous_binding = self._vector_term_bindings.get(binding_name)
            self._vector_term_bindings[binding_name] = node.var_value
            try:
                return node.body.accept(self)
            finally:
                if previous_binding is None:
                    self._vector_term_bindings.pop(binding_name, None)
                else:
                    self._vector_term_bindings[binding_name] = previous_binding
        if isinstance(node.var_value, LLVMVectorFilter) and uses_filter_size_var(node.body, binding_name):
            previous_binding = self._vector_term_bindings.get(binding_name)
            self._vector_term_bindings[binding_name] = node.var_value
            try:
                return node.body.accept(self)
            finally:
                if previous_binding is None:
                    self._vector_term_bindings.pop(binding_name, None)
                else:
                    self._vector_term_bindings[binding_name] = previous_binding

        previous_binding = self._vector_term_bindings.get(binding_name)
        self._vector_term_bindings[binding_name] = node.var_value
        try:
            return super().visit_let(node)
        finally:
            if previous_binding is None:
                self._vector_term_bindings.pop(binding_name, None)
            else:
                self._vector_term_bindings[binding_name] = previous_binding

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

    def _get_cuda_barrier_in_builder(self, builder: ir.IRBuilder) -> ir.Function:
        name = "llvm.nvvm.barrier0"
        if name in self.module.globals:
            return self.module.globals[name]
        return ir.Function(self.module, ir.FunctionType(ir.VoidType(), []), name=name)

    def _get_global_id(self) -> ir.Value:
        return self._get_cuda_id_in_builder(self.builder)

    def visit_vector_filter(self, node: LLVMVectorFilter) -> ir.Value:
        res_ty, v, size = node.type, node.v, node.size
        self._is_top_level = False
        v_val, size_val = v.accept(self), size.accept(self)

        size_ty = size_val.type
        if isinstance(size_ty, ir.PointerType) and isinstance(size_ty.pointee, ir.FunctionType):
            size_val = self.builder.call(size_val, [self.builder.bitcast(v_val, ir.PointerType(ir.IntType(8)))])

        res_base_ty = self.to_ir_type(res_ty.element_type if isinstance(res_ty, LLVMPointerType) else res_ty)
        if isinstance(res_base_ty, ir.VoidType):
            res_base_ty = ir.IntType(32)

        new_v = self._temp_alloc(res_base_ty, size_val)

        if self.vector_op_depth > 0:
            i32 = ir.IntType(32)
            one = ir.Constant(i32, 1)
            zero = ir.Constant(i32, 0)
            mask_v = self._temp_alloc(i32, size_val)

            def mask_body(idx):
                val = self.builder.load(self.builder.gep(v_val, [idx]))
                keep = self._inline_or_call(node.f, [val])
                mask = self.builder.select(self._cast_if_needed(keep, ir.IntType(1)), one, zero)
                self.builder.store(mask, self.builder.gep(mask_v, [idx]))

            self.to_ir_loop(size_val, "filter_mask", mask_body)

            scan_acc = self.builder.alloca(i32, name="filter_scan_acc")
            self.builder.store(zero, scan_acc)

            def scan_body(idx):
                curr = self.builder.load(self.builder.gep(mask_v, [idx]))
                acc = self.builder.load(scan_acc)
                self.builder.store(acc, self.builder.gep(mask_v, [idx]))
                self.builder.store(self.builder.add(acc, curr), scan_acc)

            self.to_ir_loop(size_val, "filter_scan", scan_body)

            def scatter_body(idx):
                val = self.builder.load(self.builder.gep(v_val, [idx]))
                keep = self._inline_or_call(node.f, [val])
                with self.builder.if_then(self._cast_if_needed(keep, ir.IntType(1))):
                    out_idx = self.builder.load(self.builder.gep(mask_v, [idx]))
                    self.builder.store(self._cast_if_needed(val, res_base_ty), self.builder.gep(new_v, [out_idx]))

            self.to_ir_loop(size_val, "filter_scatter", scatter_body)
            return new_v

        idx = self._get_global_id()
        out_count = self.builder.alloca(ir.IntType(32), name="filter_out_count")
        with self.builder.if_then(self.builder.icmp_signed("==", idx, ir.Constant(ir.IntType(32), 0))):
            self.builder.store(ir.Constant(ir.IntType(32), 0), out_count)

        self.builder.call(self._get_cuda_barrier_in_builder(self.builder), [])

        with self.builder.if_then(self.builder.icmp_signed("<", idx, size_val)):
            val = self.builder.load(self.builder.gep(v_val, [idx]))
            keep = self._inline_or_call(node.f, [val])
            with self.builder.if_then(self._cast_if_needed(keep, ir.IntType(1))):
                out_idx = self.builder.atomic_rmw("add", out_count, ir.Constant(ir.IntType(32), 1), "monotonic")
                self.builder.store(self._cast_if_needed(val, res_base_ty), self.builder.gep(new_v, [out_idx]))

        self.builder.call(self._get_cuda_barrier_in_builder(self.builder), [])
        return new_v

    def visit_vector_reduce(self, node: LLVMVectorReduce) -> ir.Value:
        ty, f, initial, v, size = node.type, node.f, node.initial, node.v, node.size
        self._is_top_level = False
        f_val, init_val, v_val, size_val = f.accept(self), initial.accept(self), v.accept(self), size.accept(self)

        size_ty = size_val.type
        if isinstance(size_ty, ir.PointerType) and isinstance(size_ty.pointee, ir.FunctionType):
            size_val = self.builder.call(size_val, [self.builder.bitcast(v_val, ir.PointerType(ir.IntType(8)))])

        acc_ty = self.to_ir_type(ty.element_type if isinstance(ty, LLVMPointerType) else ty)
        if isinstance(acc_ty, ir.VoidType):
            acc_ty = ir.IntType(32)

        work_v = self._temp_alloc(acc_ty, size_val)

        def copy_body(idx):
            src_val = self.builder.load(self.builder.gep(v_val, [idx]))
            self.builder.store(self._cast_if_needed(src_val, acc_ty), self.builder.gep(work_v, [idx]))

        self.to_ir_loop(size_val, "reduce_copy", copy_body)

        curr_size_ptr = self.builder.alloca(ir.IntType(32), name="reduce_curr_size")
        self.builder.store(self._cast_if_needed(size_val, ir.IntType(32)), curr_size_ptr)

        cond_bb = self.builder.append_basic_block("reduce_tree_cond")
        body_bb = self.builder.append_basic_block("reduce_tree_body")
        end_bb = self.builder.append_basic_block("reduce_tree_end")
        self.builder.branch(cond_bb)

        self.builder.position_at_end(cond_bb)
        curr_size = self.builder.load(curr_size_ptr)
        has_more = self.builder.icmp_signed(">", curr_size, ir.Constant(ir.IntType(32), 1))
        self.builder.cbranch(has_more, body_bb, end_bb)

        self.builder.position_at_end(body_bb)
        pair_count = self.builder.udiv(curr_size, ir.Constant(ir.IntType(32), 2))
        has_odd = self.builder.and_(curr_size, ir.Constant(ir.IntType(32), 1))

        def pair_reduce_body(idx):
            left_idx = self.builder.mul(idx, ir.Constant(ir.IntType(32), 2))
            right_idx = self.builder.add(left_idx, ir.Constant(ir.IntType(32), 1))
            left = self.builder.load(self.builder.gep(work_v, [left_idx]))
            right = self.builder.load(self.builder.gep(work_v, [right_idx]))
            reduced = self.builder.call(f_val, [left, right])
            self.builder.store(self._cast_if_needed(reduced, acc_ty), self.builder.gep(work_v, [idx]))

        self.to_ir_loop(pair_count, "reduce_tree_pairs", pair_reduce_body)

        with self.builder.if_then(self.builder.icmp_signed("==", has_odd, ir.Constant(ir.IntType(32), 1))):
            last_idx = self.builder.sub(curr_size, ir.Constant(ir.IntType(32), 1))
            last_val = self.builder.load(self.builder.gep(work_v, [last_idx]))
            self.builder.store(last_val, self.builder.gep(work_v, [pair_count]))

        next_size = self.builder.add(pair_count, has_odd)
        self.builder.store(next_size, curr_size_ptr)
        self.builder.branch(cond_bb)

        self.builder.position_at_end(end_bb)
        is_empty = self.builder.icmp_signed("==", self.builder.load(curr_size_ptr), ir.Constant(ir.IntType(32), 0))
        acc_ptr = self.builder.alloca(acc_ty, name="reduce_acc")
        with self.builder.if_else(is_empty) as (then_empty, else_nonempty):
            with then_empty:
                self.builder.store(self._cast_if_needed(init_val, acc_ty), acc_ptr)
            with else_nonempty:
                tree_res = self.builder.load(self.builder.gep(work_v, [ir.Constant(ir.IntType(32), 0)]))
                folded = self.builder.call(f_val, [self._cast_if_needed(init_val, acc_ty), tree_res])
                self.builder.store(self._cast_if_needed(folded, acc_ty), acc_ptr)

        new_v = self._temp_alloc(acc_ty, ir.Constant(ir.IntType(32), 1))
        self.builder.store(self.builder.load(acc_ptr), self.builder.gep(new_v, [ir.Constant(ir.IntType(32), 0)]))
        return new_v

    def visit_vector_size(self, node: LLVMVectorSize) -> ir.Value:
        filter_node: LLVMVectorFilter | None = None
        if isinstance(node.v, LLVMVectorFilter):
            filter_node = node.v
        elif isinstance(node.v, LLVMCast) and isinstance(node.v.val, LLVMVectorFilter):
            filter_node = node.v.val
        elif isinstance(node.v, LLVMVar):
            bound = self._vector_term_bindings.get(sanitize_name(node.v.name))
            if isinstance(bound, LLVMVectorFilter):
                filter_node = bound
            elif isinstance(bound, LLVMCast) and isinstance(bound.val, LLVMVectorFilter):
                filter_node = bound.val

        if filter_node is not None:
            v_val = filter_node.v.accept(self)
            size_val = filter_node.size.accept(self)
            count_ptr = self.builder.alloca(ir.IntType(32), name="filter_size_res")
            self.builder.store(ir.Constant(ir.IntType(32), 0), count_ptr)

            def body(idx):
                val = self.builder.load(self.builder.gep(v_val, [idx]))
                keep = self._inline_or_call(filter_node.f, [val])
                with self.builder.if_then(self._cast_if_needed(keep, ir.IntType(1))):
                    curr = self.builder.load(count_ptr)
                    self.builder.store(self.builder.add(curr, ir.Constant(ir.IntType(32), 1)), count_ptr)

            self.to_ir_loop(size_val, "filter_size_count", body)
            return self.builder.load(count_ptr)

        raise LLVMIRGenerationError("unsupported CUDA vector size")
