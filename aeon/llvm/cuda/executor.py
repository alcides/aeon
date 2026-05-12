from __future__ import annotations

import hashlib
from typing import Any, Sequence

import llvmlite.binding as llvm
import numpy as np
from loguru import logger

try:
    import cupy as cp
except ImportError:
    cp = None

from aeon.llvm.core import LLVMExecutionEngine, LLVMBackendError
from aeon.llvm.constants import LLVMMetadataKey, metadata_get, metadata_has
from aeon.llvm.cuda.plan import (
    PLAN_ARRAYS_KEY,
    PLAN_SIZE_DIM,
    RESULT_BUFFER_DTYPE,
    CudaBufferName,
    CudaCommonKernelName,
    CudaKernelPlan,
    CudaKernelStep,
    CudaPlanAlgorithm,
    CudaStepArgs,
    CudaTempSpec,
    count_map_kernel_name,
    filter_mask_kernel_name,
    filter_scatter_kernel_name,
    reduce_copy_kernel_name,
    reduce_finish_kernel_name,
    reduce_step_kernel_name,
)
from aeon.llvm.utils import RawVector, VectorDType, sanitize_name
from aeon.llvm.llvm_ast import (
    LLVMType,
    LLVMPointerType,
    LLVMIntType,
    LLVMFloatType,
    LLVMDoubleType,
    LLVMVoidType,
)


class CUDAExecutionError(LLVMBackendError):
    pass


class CUDALLVMExecutionEngine(LLVMExecutionEngine):
    def __init__(self) -> None:
        self._module_cache: dict[str, str] = {}
        self._temp_pool: dict[tuple[str, tuple[int, ...]], Any] = {}

    def _acquire_temp(self, key: str, shape: tuple[int, ...], dtype: str) -> Any:
        if cp is None:
            raise CUDAExecutionError("cupy is not installed")
        pool_key = (f"{key}:{dtype}", shape)
        temp = self._temp_pool.get(pool_key)
        if temp is None:
            temp = cp.empty(shape, dtype=dtype)
            self._temp_pool[pool_key] = temp
        return temp

    def _dtype_for_pointer(self, ty: LLVMPointerType) -> str:
        if isinstance(ty.element_type, LLVMIntType):
            return f"int{ty.element_type.bits}"
        if isinstance(ty.element_type, LLVMFloatType):
            return "float32"
        if isinstance(ty.element_type, LLVMDoubleType):
            return "float64"
        return "int32"

    def _normalize_pointer_arg(self, arg: Any, ty: LLVMPointerType) -> tuple[Any, Any | None, int]:
        if cp is None:
            raise CUDAExecutionError("cupy is not installed")
        dtype = self._dtype_for_pointer(ty)
        if isinstance(arg, RawVector):
            arg._ensure_not_freed()
            if arg.dtype == VectorDType.OBJECT or arg.arr is None:
                raise CUDAExecutionError("object vector is not supported")
            host_arr = arg.arr
            gpu_arr = cp.asarray(host_arr)
            return gpu_arr, host_arr, int(arg.size)
        if isinstance(arg, cp.ndarray):
            return arg, None, int(arg.size)
        if isinstance(arg, np.ndarray):
            gpu_arr = cp.asarray(arg.astype(dtype, copy=False))
            return gpu_arr, arg, int(arg.size)
        if isinstance(arg, list):
            gpu_arr = cp.asarray(np.asarray(arg, dtype=dtype))
            return gpu_arr, arg, len(arg)
        if hasattr(arg, "__cuda_array_interface__"):
            gpu_arr = cp.asarray(arg)
            return gpu_arr, None, int(gpu_arr.size)
        raise CUDAExecutionError(f"unsupported pointer arg: {type(arg).__name__}")

    def _select_cuda_arch(self, metadata: dict[str, Any]) -> str:
        requested = metadata_get(metadata, LLVMMetadataKey.GPU_ARCH)
        if requested:
            return str(requested)
        if cp is not None:
            try:
                props = cp.cuda.runtime.getDeviceProperties(0)
                major, minor = props["major"], props["minor"]
                return f"sm_{major}{minor}"
            except Exception:
                pass
        return "sm_86"

    def _parse_plan(self, raw_plan: Any, lookup_name: str, block_size: int) -> CudaKernelPlan | None:
        if isinstance(raw_plan, CudaKernelPlan):
            return raw_plan
        if isinstance(raw_plan, dict):
            return CudaKernelPlan.from_dict(raw_plan)
        if isinstance(raw_plan, list) and raw_plan:
            steps = tuple(
                CudaKernelStep(
                    kernel=str(step.get("kernel", lookup_name)),
                    block_size=int(step.get("block_size", block_size)) if step.get("block_size") is not None else None,
                    grid_size=int(step["grid_size"]) if step.get("grid_size") is not None else None,
                    args=step.get("args", CudaStepArgs.CALL),
                )
                for step in raw_plan
                if isinstance(step, dict)
            )
            return CudaKernelPlan(function=lookup_name, steps=steps)
        return None

    def _resolve_shape(self, shape: Sequence[str | int], size: int) -> tuple[int, ...]:
        resolved = []
        for dim in shape:
            resolved.append(size if dim == PLAN_SIZE_DIM else int(dim))
        return tuple(resolved)

    def _allocate_plan_buffers(self, plan: CudaKernelPlan, size: int) -> dict[str, Any]:
        runtime_env: dict[str, Any] = {}
        arrays: dict[str, Any] = {}
        for buffer in plan.buffers:
            dtype = "int32" if buffer.dtype == RESULT_BUFFER_DTYPE else buffer.dtype
            key = f"{plan.function}:{buffer.name}:{dtype}:{buffer.shape}:{buffer.generation}"
            array = self._acquire_temp(key, self._resolve_shape(buffer.shape, size), dtype)
            runtime_env[buffer.name] = array.data.ptr
            arrays[buffer.name] = array
        runtime_env[PLAN_ARRAYS_KEY] = arrays
        return runtime_env

    def _block_size(self, metadata: dict[str, Any], fallback: int = 256) -> int:
        return max(1, int(metadata_get(metadata, LLVMMetadataKey.GPU_BLOCK_SIZE, fallback)))

    def _execute_count_tree(
        self,
        plan: CudaKernelPlan,
        resolve_kernel,
        runtime_env: dict[str, Any],
        processed_args: list[Any],
        arg_count: int,
        scalar_out_gpu: Any,
        size: int,
        metadata: dict[str, Any],
        block_size: int,
    ) -> None:
        if scalar_out_gpu is None:
            raise CUDAExecutionError("missing scalar output")
        map_kernel = resolve_kernel(count_map_kernel_name(plan.function))
        reduce_kernel = resolve_kernel(CudaCommonKernelName.REDUCE_I32_STEP.value)
        final_kernel = resolve_kernel(CudaCommonKernelName.STORE_I32_RESULT.value)
        if map_kernel is None or reduce_kernel is None or final_kernel is None:
            raise CUDAExecutionError("missing count kernels")

        flags_ptr = runtime_env[CudaBufferName.COUNT_FLAGS.value]
        ping_ptr = runtime_env[CudaBufferName.REDUCE_PING.value]
        map_block = self._block_size(metadata, block_size)
        map_grid = max(1, (size + map_block - 1) // map_block)
        map_kernel((map_grid,), (map_block,), tuple(processed_args[:arg_count] + [flags_ptr]))

        if size <= 0:
            scalar_out_gpu.fill(0)
            return

        src_ptr, dst_ptr = flags_ptr, ping_ptr
        curr_n = int(size)
        while curr_n > 1:
            out_n = (curr_n + 1) // 2
            grid = max(1, (out_n + map_block - 1) // map_block)
            reduce_kernel((grid,), (map_block,), (src_ptr, dst_ptr, np.int32(curr_n)))
            src_ptr, dst_ptr = dst_ptr, src_ptr
            curr_n = out_n
        final_kernel((1,), (1,), (src_ptr, scalar_out_gpu.data.ptr))

    def _execute_reduce_tree(
        self,
        plan: CudaKernelPlan,
        resolve_kernel,
        runtime_env: dict[str, Any],
        processed_args: list[Any],
        arg_count: int,
        scalar_out_gpu: Any,
        size: int,
        metadata: dict[str, Any],
        block_size: int,
    ) -> Any | None:
        copy_kernel = resolve_kernel(reduce_copy_kernel_name(plan.function))
        reduce_kernel = resolve_kernel(reduce_step_kernel_name(plan.function))
        finish_kernel = resolve_kernel(reduce_finish_kernel_name(plan.function))
        if copy_kernel is None or reduce_kernel is None or finish_kernel is None:
            raise CUDAExecutionError("missing reduce kernels")

        arrays = runtime_env[PLAN_ARRAYS_KEY]
        work = arrays[CudaBufferName.REDUCE_WORK.value]
        ping = arrays[CudaBufferName.REDUCE_PING.value]
        out = arrays[CudaBufferName.REDUCE_OUT.value]
        reduce_block = self._block_size(metadata, block_size)
        src_ptr, dst_ptr = work.data.ptr, ping.data.ptr

        if size > 0:
            grid = max(1, (size + reduce_block - 1) // reduce_block)
            copy_kernel((grid,), (reduce_block,), tuple(processed_args[:arg_count] + [src_ptr]))

        curr_n = int(size)
        while curr_n > 1:
            out_n = (curr_n + 1) // 2
            grid = max(1, (out_n + reduce_block - 1) // reduce_block)
            reduce_kernel((grid,), (reduce_block,), (src_ptr, dst_ptr, np.int32(curr_n)))
            src_ptr, dst_ptr = dst_ptr, src_ptr
            curr_n = out_n

        out_ptr = scalar_out_gpu.data.ptr if scalar_out_gpu is not None else out.data.ptr
        finish_kernel((1,), (1,), tuple(processed_args[:arg_count] + [src_ptr, out_ptr]))
        return out if scalar_out_gpu is None else None

    def _execute_filter_plan(
        self,
        plan: CudaKernelPlan,
        resolve_kernel,
        runtime_env: dict[str, Any],
        processed_args: list[Any],
        arg_count: int,
        scalar_out_gpu: Any,
        size: int,
        metadata: dict[str, Any],
        block_size: int,
    ) -> tuple[Any, Any, int] | None:
        mask_kernel = resolve_kernel(filter_mask_kernel_name(plan.function))
        scan_kernel = resolve_kernel(CudaCommonKernelName.SCAN_I32_INCLUSIVE_STEP.value)
        scatter_kernel = resolve_kernel(filter_scatter_kernel_name(plan.function))
        last_kernel = resolve_kernel(CudaCommonKernelName.STORE_I32_LAST.value)
        if mask_kernel is None or scan_kernel is None:
            raise CUDAExecutionError("missing filter scan kernels")
        if plan.algorithm == CudaPlanAlgorithm.FILTER_COMPACT and scatter_kernel is None:
            raise CUDAExecutionError("missing filter scatter kernel")
        if plan.algorithm == CudaPlanAlgorithm.FILTER_SIZE_SCAN and (last_kernel is None or scalar_out_gpu is None):
            raise CUDAExecutionError("missing filter size kernel")

        arrays = runtime_env[PLAN_ARRAYS_KEY]
        mask = arrays[CudaBufferName.FILTER_MASK.value]
        scan = arrays[CudaBufferName.FILTER_SCAN.value]
        out = arrays.get(CudaBufferName.FILTER_OUT.value)
        filter_block = self._block_size(metadata, block_size)
        grid = max(1, (size + filter_block - 1) // filter_block)
        mask_kernel((grid,), (filter_block,), tuple(processed_args[:arg_count] + [mask.data.ptr]))

        scan_src = mask
        scan_dst = scan
        offset = 1
        while offset < max(1, int(size)):
            scan_kernel(
                (grid,),
                (filter_block,),
                (scan_src.data.ptr, scan_dst.data.ptr, np.int32(size), np.int32(offset)),
            )
            scan_src, scan_dst = scan_dst, scan_src
            offset *= 2

        if plan.algorithm == CudaPlanAlgorithm.FILTER_SIZE_SCAN:
            last_kernel((1,), (1,), (scan_src.data.ptr, scalar_out_gpu.data.ptr, np.int32(size)))
            return None

        scatter_kernel(
            (grid,),
            (filter_block,),
            tuple(processed_args[:arg_count] + [scan_src.data.ptr, mask.data.ptr, out.data.ptr]),
        )
        return out, scan_src, int(size)

    def _execute_generic_plan(
        self,
        plan: CudaKernelPlan,
        resolve_kernel,
        runtime_env: dict[str, Any],
        processed_args: list[Any],
        size: int,
        block_size: int,
    ) -> None:
        for step in plan.steps:
            step_kernel = resolve_kernel(step.kernel)
            if step_kernel is None:
                raise CUDAExecutionError(f"missing kernel step: {step.kernel}")

            step_block = step.block_size or block_size
            step_grid = int(step.grid_size if step.grid_size is not None else (size + step_block - 1) // step_block)
            launch_args = self._resolve_step_args(step, runtime_env, processed_args, size)
            step_kernel((step_grid,), (step_block,), tuple(launch_args))

    def _resolve_step_args(
        self, step: CudaKernelStep, runtime_env: dict[str, Any], processed_args: list[Any], size: int
    ) -> list[Any]:
        if step.args == CudaStepArgs.CALL:
            return list(processed_args)

        launch_args: list[Any] = []
        for spec in step.args:
            if isinstance(spec, str) and spec in runtime_env:
                launch_args.append(runtime_env[spec])
            elif spec in (CudaTempSpec.I32, CudaTempSpec.I32.value):
                temp = self._acquire_temp(CudaTempSpec.I32.pool_key, (size,), CudaTempSpec.I32.dtype)
                runtime_env[CudaTempSpec.I32.value] = temp.data.ptr
                launch_args.append(temp.data.ptr)
            elif spec in (CudaTempSpec.F32, CudaTempSpec.F32.value):
                temp = self._acquire_temp(CudaTempSpec.F32.pool_key, (size,), CudaTempSpec.F32.dtype)
                runtime_env[CudaTempSpec.F32.value] = temp.data.ptr
                launch_args.append(temp.data.ptr)
            elif spec == PLAN_SIZE_DIM:
                launch_args.append(np.int32(size))
            else:
                launch_args.append(spec)
        return launch_args

    def execute(
        self,
        llvm_ir: str,
        func_name: str,
        args: list[Any],
        arg_types: list[LLVMType],
        ret_type: LLVMType,
        metadata: dict[str, Any] | None = None,
    ) -> Any:
        if cp is None:
            raise CUDAExecutionError("cupy is not installed")

        metadata = metadata or {}
        is_debug: bool = bool(metadata_get(metadata, LLVMMetadataKey.GPU_DEBUG, False))

        if is_debug:
            self._write_ir_to_file(llvm_ir, "debug_llvm.ll")

        ir_hash = hashlib.md5(llvm_ir.encode("utf-8")).hexdigest()

        if ir_hash not in self._module_cache:
            ptx = self._compile_to_ptx(llvm_ir, metadata)
            self._module_cache[ir_hash] = ptx

            if is_debug:
                self._write_ir_to_file(ptx, "debug.ptx")

        ptx = self._module_cache[ir_hash]
        no_device_alloc = bool(metadata_get(metadata, LLVMMetadataKey.GPU_NO_DEVICE_ALLOC, True))
        if no_device_alloc:
            alloc_markers = ("malloc", "free", "alloca.u64")
            if any(m in ptx for m in alloc_markers):
                raise CUDAExecutionError("device allocation is disabled")

        lookup_name = func_name
        if not isinstance(func_name, str):
            lookup_name = sanitize_name(func_name)

        processed_args: list[Any] = []
        gpu_arrays: list[tuple[Any, Any | None]] = []
        size = 1

        for i, (arg, ty) in enumerate(zip(args, arg_types)):
            if isinstance(ty, LLVMPointerType):
                gpu_arr, original, arg_size = self._normalize_pointer_arg(arg, ty)
                gpu_arrays.append((gpu_arr, original))
                processed_args.append(gpu_arr.data.ptr)
                size = max(size, arg_size)
            elif isinstance(ty, LLVMIntType):
                val = np.int32(arg) if ty.bits <= 32 else np.int64(arg)
                processed_args.append(val)
            elif isinstance(ty, (LLVMFloatType, LLVMDoubleType)):
                val = np.float32(arg) if isinstance(ty, LLVMFloatType) else np.float64(arg)
                processed_args.append(val)
            else:
                processed_args.append(arg)

        has_scalar_return = not isinstance(ret_type, (LLVMVoidType, LLVMPointerType))
        scalar_out_gpu = None
        if has_scalar_return:
            if isinstance(ret_type, LLVMIntType):
                dtype = f"int{ret_type.bits}"
            elif isinstance(ret_type, LLVMFloatType):
                dtype = "float32"
            elif isinstance(ret_type, LLVMDoubleType):
                dtype = "float64"
            else:
                dtype = "int32"
            scalar_out_gpu = cp.zeros(1, dtype=dtype)
            processed_args.append(scalar_out_gpu.data.ptr)

        if metadata_has(metadata, LLVMMetadataKey.SIZE):
            size = metadata_get(metadata, LLVMMetadataKey.SIZE)

        block_size = self._block_size(metadata)
        grid_size = (size + block_size - 1) // block_size
        if has_scalar_return:
            block_size = 1
            grid_size = 1

        mod = None
        return_vector_gpu = None
        filter_return_info = None
        try:
            mod = cp.cuda.Module()
            mod.load(ptx.encode("utf-8"))

            entry_points = [line.split()[2] for line in ptx.split("\n") if ".visible .entry" in line]

            def resolve_kernel(name: str) -> Any | None:
                possible_names = [name, f"{name}_kernel", lookup_name, f"{lookup_name}_kernel", str(func_name)]
                possible_names.extend(entry_points)
                for candidate in possible_names:
                    try:
                        name_clean = candidate.split("(")[0] if "(" in candidate else candidate
                        return mod.get_function(name_clean)
                    except Exception:
                        continue
                return None

            kernel_plan = self._parse_plan(
                metadata_get(metadata, LLVMMetadataKey.GPU_KERNEL_PLAN),
                lookup_name,
                block_size,
            )
            if kernel_plan is not None and kernel_plan.steps:
                runtime_env = self._allocate_plan_buffers(kernel_plan, size)

                if kernel_plan.algorithm == CudaPlanAlgorithm.COUNT_TREE_I32:
                    self._execute_count_tree(
                        kernel_plan,
                        resolve_kernel,
                        runtime_env,
                        processed_args,
                        len(arg_types),
                        scalar_out_gpu,
                        size,
                        metadata,
                        block_size,
                    )
                elif kernel_plan.algorithm == CudaPlanAlgorithm.REDUCE_TREE:
                    return_vector_gpu = self._execute_reduce_tree(
                        kernel_plan,
                        resolve_kernel,
                        runtime_env,
                        processed_args,
                        len(arg_types),
                        scalar_out_gpu,
                        size,
                        metadata,
                        block_size,
                    )
                elif kernel_plan.algorithm in {
                    CudaPlanAlgorithm.FILTER_COMPACT,
                    CudaPlanAlgorithm.FILTER_SIZE_SCAN,
                }:
                    filter_return_info = self._execute_filter_plan(
                        kernel_plan,
                        resolve_kernel,
                        runtime_env,
                        processed_args,
                        len(arg_types),
                        scalar_out_gpu,
                        size,
                        metadata,
                        block_size,
                    )
                else:
                    self._execute_generic_plan(
                        kernel_plan,
                        resolve_kernel,
                        runtime_env,
                        processed_args,
                        size,
                        block_size,
                    )
            else:
                raw_kernel = resolve_kernel(lookup_name)
                if raw_kernel is None:
                    raise CUDAExecutionError(f"kernel not found: {func_name}")

                raw_kernel((grid_size,), (block_size,), tuple(processed_args))
        except Exception as e:
            logger.debug(f"Kernel launch failed for {func_name}. PTX content:\n{ptx}")
            raise CUDAExecutionError(f"kernel launch failed: {e}")

        cp.cuda.Stream.null.synchronize()

        if has_scalar_return:
            val = scalar_out_gpu.get()[0]
            if isinstance(val, (np.integer, np.floating)):
                return val.item()
            return val

        if return_vector_gpu is not None:
            return RawVector.from_numpy(return_vector_gpu.get())

        if filter_return_info is not None:
            out, scan_src, logical_capacity = filter_return_info
            if logical_capacity <= 0:
                return RawVector.from_numpy(out[:0].get())
            logical_size = int(scan_src[logical_capacity - 1].get())
            return RawVector.from_numpy(out[:logical_size].get())

        if isinstance(ret_type, LLVMPointerType) and gpu_arrays:
            res_gpu, _ = gpu_arrays[0]
            return RawVector.from_numpy(res_gpu.get())

        if gpu_arrays:
            res_gpu, _ = gpu_arrays[0]
            return RawVector.from_numpy(res_gpu.get())

        return None

    def _write_ir_to_file(self, ir: str, filename: str):
        with open(filename, "w") as f:
            f.write(ir)

    def _compile_to_ptx(self, llvm_ir: str, metadata: dict[str, Any]) -> str:
        llvm.initialize_all_targets()
        llvm.initialize_all_asmprinters()
        mod = llvm.parse_assembly(llvm_ir)
        mod.verify()
        target = llvm.Target.from_triple("nvptx64-nvidia-cuda")
        cuda_opt_level = int(metadata_get(metadata, LLVMMetadataKey.GPU_OPT_LEVEL, 0))
        tm = target.create_target_machine(cpu=self._select_cuda_arch(metadata), features="+ptx73", opt=cuda_opt_level)
        pto = llvm.create_pipeline_tuning_options(speed_level=cuda_opt_level)
        pb = llvm.create_pass_builder(tm, pto)
        pm = pb.getModulePassManager()
        pm.run(mod, pb)
        return str(tm.emit_assembly(mod))
