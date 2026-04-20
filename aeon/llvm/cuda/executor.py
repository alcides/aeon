from __future__ import annotations

import ctypes
import os
from typing import Any, List

import llvmlite.binding as llvm
from loguru import logger

from aeon.llvm.core import LLVMExecutionEngine, LLVMBackendError
from aeon.llvm.llvm_ast import LLVMType, LLVMPointerType


class CUDAExecutionError(LLVMBackendError):
    pass


class CUDAExecutionEngine(LLVMExecutionEngine):
    def __init__(self):
        try:
            self.libcuda = self._load_cuda_library()
            self._init_cuda()
            self.device = self._get_device(0)
            self.context = self._create_context(self.device)
            self._setup_api()
            self._module_cache = {}
            logger.info("Successfully initialized CUDA backend.")
        except Exception as e:
            raise CUDAExecutionError(f"Failed to initialize CUDA: {e}")

    def _setup_api(self):
        # mem management
        self.libcuda.cuMemAlloc_v2.argtypes = [ctypes.POINTER(ctypes.c_void_p), ctypes.c_size_t]
        self.libcuda.cuMemFree_v2.argtypes = [ctypes.c_void_p]
        self.libcuda.cuMemcpyHtoD_v2.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_size_t]
        self.libcuda.cuMemcpyDtoH_v2.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_size_t]

        # kernel launch
        self.libcuda.cuLaunchKernel.argtypes = [
            ctypes.c_void_p,
            ctypes.c_uint,
            ctypes.c_uint,
            ctypes.c_uint,
            ctypes.c_uint,
            ctypes.c_uint,
            ctypes.c_uint,
            ctypes.c_uint,
            ctypes.c_void_p,
            ctypes.POINTER(ctypes.c_void_p),
            ctypes.POINTER(ctypes.c_void_p),
        ]

        self.libcuda.cuCtxSynchronize.argtypes = []
        self.libcuda.cuModuleLoadData.argtypes = [ctypes.POINTER(ctypes.c_void_p), ctypes.c_void_p]
        self.libcuda.cuModuleGetFunction.argtypes = [ctypes.POINTER(ctypes.c_void_p), ctypes.c_void_p, ctypes.c_char_p]

        self.libcuda.cuLinkCreate_v2.argtypes = [
            ctypes.c_uint,
            ctypes.c_void_p,
            ctypes.c_void_p,
            ctypes.POINTER(ctypes.c_void_p),
        ]
        self.libcuda.cuLinkAddData_v2.argtypes = [
            ctypes.c_void_p,
            ctypes.c_int,
            ctypes.c_void_p,
            ctypes.c_size_t,
            ctypes.c_char_p,
            ctypes.c_uint,
            ctypes.c_void_p,
            ctypes.c_void_p,
        ]
        self.libcuda.cuLinkComplete.argtypes = [
            ctypes.c_void_p,
            ctypes.POINTER(ctypes.c_void_p),
            ctypes.POINTER(ctypes.c_size_t),
        ]
        self.libcuda.cuLinkDestroy.argtypes = [ctypes.c_void_p]

    def _load_cuda_library(self):
        paths = [
            "libcuda.so",
            "/usr/lib/x86_64-linux-gnu/libcuda.so",
            "/usr/local/cuda/lib64/libcuda.so",
            "nvcuda.dll",
        ]
        for path in paths:
            try:
                lib = ctypes.CDLL(path)
                logger.debug(f"loaded CUDA driver from {path}")
                return lib
            except OSError:
                continue
        raise CUDAExecutionError("CUDA driver library not found.")

    def _init_cuda(self):
        if self.libcuda.cuInit(0) != 0:
            raise CUDAExecutionError("cuInit failed")

    def _get_device(self, ordinal: int):
        device = ctypes.c_int()
        if self.libcuda.cuDeviceGet(ctypes.byref(device), ordinal) != 0:
            raise CUDAExecutionError("cuDeviceGet failed")
        return device

    def _create_context(self, device):
        context = ctypes.c_void_p()
        if self.libcuda.cuCtxCreate(ctypes.byref(context), 0, device) != 0:
            raise CUDAExecutionError("cuCtxCreate failed")
        return context

    def execute(
        self,
        llvm_ir: str,
        func_name: str,
        args: List[Any],
        arg_types: List[LLVMType],
        ret_type: LLVMType,
    ) -> Any:
        logger.debug(f"Executing kernel {func_name} on GPU.")

        ir_hash = hash(llvm_ir)
        if ir_hash not in self._module_cache:
            ptx = self._compile_to_ptx(llvm_ir)
            self._module_cache[ir_hash] = self._load_module(ptx)

        module = self._module_cache[ir_hash]
        function = self._get_function(module, func_name)

        device_ptrs = []
        kernel_params = []
        cleanup_tasks = []

        try:
            for arg, ty in zip(args, arg_types):
                if isinstance(ty, LLVMPointerType):
                    cty = self._get_ctypes_type(ty.element_type)
                    data = (cty * len(arg))(*arg)
                    size = ctypes.sizeof(data)
                    d_ptr = ctypes.c_void_p()
                    if self.libcuda.cuMemAlloc_v2(ctypes.byref(d_ptr), size) != 0:
                        raise CUDAExecutionError("cuMemAlloc failed")
                    if self.libcuda.cuMemcpyHtoD_v2(d_ptr, ctypes.cast(data, ctypes.c_void_p), size) != 0:
                        raise CUDAExecutionError("cuMemcpyHtoD failed")
                    device_ptrs.append(d_ptr)
                    kernel_params.append(ctypes.addressof(d_ptr))
                    cleanup_tasks.append((d_ptr, data, size, arg))
                else:
                    c_val = self._get_ctypes_type(ty)(arg)
                    kernel_params.append(ctypes.addressof(c_val))

            params_ptr = (ctypes.c_void_p * len(kernel_params))(*[ctypes.c_void_p(p) for p in kernel_params])

            if self.libcuda.cuLaunchKernel(function, 1, 1, 1, 1, 1, 1, 0, None, params_ptr, None) != 0:
                raise CUDAExecutionError(f"cuLaunchKernel failed for {func_name}")

            if self.libcuda.cuCtxSynchronize() != 0:
                raise CUDAExecutionError(f"cuCtxSynchronize failed during {func_name} execution")

            for d_ptr, host_data, size, original_arg in cleanup_tasks:
                if self.libcuda.cuMemcpyDtoH_v2(ctypes.cast(host_data, ctypes.c_void_p), d_ptr, size) != 0:
                    raise CUDAExecutionError("cuMemcpyDtoH failed")
                if isinstance(original_arg, list):
                    original_arg[:] = list(host_data)

            return None

        finally:
            for d_ptr in device_ptrs:
                self.libcuda.cuMemFree_v2(d_ptr)

    def _get_ctypes_type(self, ty: LLVMType):
        from aeon.llvm.llvm_ast import LLVMIntType, LLVMFloatType, LLVMDoubleType, LLVMBoolType

        mapping = {
            LLVMIntType: ctypes.c_int32,
            LLVMFloatType: ctypes.c_float,
            LLVMDoubleType: ctypes.c_double,
            LLVMBoolType: ctypes.c_bool,
        }
        return mapping.get(type(ty), ctypes.c_int32)

    def _compile_to_ptx(self, llvm_ir: str) -> str:
        llvm.initialize_all_targets()
        llvm.initialize_all_asmprinters()
        mod = llvm.parse_assembly(llvm_ir)
        triple = "nvptx64-nvidia-cuda"
        target = llvm.Target.from_triple(triple)
        tm = target.create_target_machine(chip="sm_35")  # sm_35+ for dynamic parallelism
        return tm.emit_assembly(mod)

    def _find_libcudadevrt(self) -> str | None:
        common_paths = [
            "/usr/local/cuda/lib64/libcudadevrt.a",
            "/usr/local/cuda/lib/libcudadevrt.a",
            "/usr/lib/x86_64-linux-gnu/libcudadevrt.a",
            os.path.join(os.environ.get("CUDA_PATH", ""), "lib/x64/libcudadevrt.lib"),
        ]
        for path in common_paths:
            if os.path.exists(path):
                logger.debug(f"Found libcudadevrt at {path}")
                return path
        logger.warning("libcudadevrt.a not found. Dynamic parallelism might fail if required.")
        return None

    def _load_module(self, ptx: str):
        logger.debug("Linking and loading CUDA module.")
        link_state = ctypes.c_void_p()
        if self.libcuda.cuLinkCreate_v2(0, None, None, ctypes.byref(link_state)) != 0:
            raise CUDAExecutionError("cuLinkCreate failed")

        try:
            ptx_bytes = ptx.encode("utf-8")
            if self.libcuda.cuLinkAddData_v2(link_state, 4, ptx_bytes, len(ptx_bytes), b"aeon.ptx", 0, None, None) != 0:
                raise CUDAExecutionError("cuLinkAddData (PTX) failed")

            devrt_path = self._find_libcudadevrt()
            if devrt_path:
                with open(devrt_path, "rb") as f:
                    devrt_data = f.read()
                    if (
                        self.libcuda.cuLinkAddData_v2(
                            link_state, 2, devrt_data, len(devrt_data), b"libcudadevrt.a", 0, None, None
                        )
                        != 0
                    ):
                        raise CUDAExecutionError("cuLinkAddData (devrt) failed")

            cubin = ctypes.c_void_p()
            size = ctypes.c_size_t()
            if self.libcuda.cuLinkComplete(link_state, ctypes.byref(cubin), ctypes.byref(size)) != 0:
                raise CUDAExecutionError("cuLinkComplete failed")

            module = ctypes.c_void_p()
            if self.libcuda.cuModuleLoadData(ctypes.byref(module), cubin) != 0:
                raise CUDAExecutionError("cuModuleLoadData failed")

            self.libcuda.cuLinkDestroy(link_state)
            return module
        except Exception as e:
            self.libcuda.cuLinkDestroy(link_state)
            raise e

    def _get_function(self, module, name: str):
        function = ctypes.c_void_p()
        if self.libcuda.cuModuleGetFunction(ctypes.byref(function), module, name.encode("utf-8")) != 0:
            raise CUDAExecutionError(f"cuModuleGetFunction failed for {name}")
        return function
