from __future__ import annotations

import hashlib
from typing import Any, List, Dict

import llvmlite.binding as llvm
import numpy as np

try:
    import cupy as cp
except ImportError:
    cp = None

from aeon.llvm.core import LLVMExecutionEngine, LLVMBackendError
from aeon.llvm.utils import sanitize_name
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
        self._module_cache: Dict[str, str] = {}

    def execute(
        self,
        llvm_ir: str,
        func_name: str,
        args: List[Any],
        arg_types: List[LLVMType],
        ret_type: LLVMType,
        metadata: dict[str, Any] | None = None,
    ) -> Any:
        if cp is None:
            raise CUDAExecutionError("cupy is not installed")

        metadata = metadata or {}
        ir_hash = hashlib.md5(llvm_ir.encode("utf-8")).hexdigest()

        if ir_hash not in self._module_cache:
            with open("debug.ll", "w") as f:
                f.write(llvm_ir)

            ptx = self._compile_to_ptx(llvm_ir, metadata)
            self._module_cache[ir_hash] = ptx

            with open("debug.ptx", "w") as f:
                f.write(ptx)

        ptx = self._module_cache[ir_hash]

        lookup_name = func_name
        if not isinstance(func_name, str):
            lookup_name = sanitize_name(func_name)

        processed_args = []
        gpu_arrays = []
        size = 1

        for i, (arg, ty) in enumerate(zip(args, arg_types)):
            if isinstance(ty, LLVMPointerType):
                if isinstance(arg, (list, np.ndarray, cp.ndarray if cp else type(None))):
                    if isinstance(ty.element_type, LLVMIntType):
                        dtype = f"int{ty.element_type.bits}"
                    elif isinstance(ty.element_type, LLVMFloatType):
                        dtype = "float32"
                    elif isinstance(ty.element_type, LLVMDoubleType):
                        dtype = "float64"
                    else:
                        dtype = "int32"

                    gpu_arr = cp.array(arg, dtype=dtype)
                    gpu_arrays.append((gpu_arr, arg))  # Keep track of original if we need to copy back
                    processed_args.append(gpu_arr.data.ptr)
                    size = max(size, len(arg))
                elif hasattr(arg, "data"):
                    processed_args.append(arg.data.ptr)
                    size = max(size, arg.size)
                else:
                    processed_args.append(int(arg))
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

        if "size" in metadata:
            size = metadata["size"]

        block_size = metadata.get("gpu_block_size", 256)
        grid_size = (size + block_size - 1) // block_size

        try:
            mod = cp.cuda.Module()
            mod.load(ptx.encode("utf-8"))

            entry_points = [line.split()[2] for line in ptx.split("\n") if ".visible .entry" in line]

            raw_kernel = None
            possible_names = [f"{lookup_name}_kernel", lookup_name, str(func_name)]
            possible_names.extend(entry_points)

            for name in possible_names:
                try:
                    name_clean = name.split("(")[0] if "(" in name else name
                    raw_kernel = mod.get_function(name_clean)
                    break
                except Exception:
                    continue

            if raw_kernel is None:
                raise CUDAExecutionError(f"No kernel found in PTX for '{func_name}'. Entry points: {entry_points}")

            raw_kernel((grid_size,), (block_size,), tuple(processed_args))
        except Exception as e:
            print(f"DEBUG: Kernel launch failed. PTX content:\n{ptx}")
            raise CUDAExecutionError(f"Kernel launch failed: {e}")

        cp.cuda.Stream.null.synchronize()

        if has_scalar_return:
            val = scalar_out_gpu.get()[0]
            if isinstance(val, (np.integer, np.floating)):
                return val.item()
            return val

        if isinstance(ret_type, LLVMPointerType) or "Vector" in str(ret_type):
            if gpu_arrays:
                res_gpu, _ = gpu_arrays[0]
                return res_gpu.get().tolist()

        if gpu_arrays:
            res_gpu, _ = gpu_arrays[0]
            return res_gpu.get().tolist()

        return None

    def _compile_to_ptx(self, llvm_ir: str, metadata: dict[str, Any]) -> str:
        llvm.initialize_all_targets()
        llvm.initialize_all_asmprinters()
        mod = llvm.parse_assembly(llvm_ir)
        mod.verify()
        target = llvm.Target.from_triple("nvptx64-nvidia-cuda")
        tm = target.create_target_machine(cpu="sm_86", opt=3)
        pto = llvm.create_pipeline_tuning_options(speed_level=3)
        pb = llvm.create_pass_builder(tm, pto)
        pm = llvm.create_new_module_pass_manager()
        pm.add_always_inliner_pass()
        pm.run(mod, pb)
        return str(tm.emit_assembly(mod))
