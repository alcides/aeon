from __future__ import annotations

import ctypes
import os
from typing import Any, List

import llvmlite.binding as llvm
from loguru import logger

from aeon.llvm.core import LLVMExecutionEngine, LLVMBackendError
from aeon.llvm.llvm_ast import LLVMType, LLVMPointerType, LLVMVoidType


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
            # Inductive ADTs allocate on the device heap; the default heap is only
            # ~8MB and deep recursion needs a larger stack than the CUDA default.
            self._configure_device_limits()
            self._module_cache = {}
            logger.info("Successfully initialized CUDA backend.")
        except Exception as e:
            raise CUDAExecutionError(f"Failed to initialize CUDA: {e}")

    def _setup_api(self):
        # mem management — CUdeviceptr is an unsigned 64-bit handle on modern drivers
        self.libcuda.cuMemAlloc_v2.argtypes = [ctypes.POINTER(ctypes.c_uint64), ctypes.c_size_t]
        self.libcuda.cuMemFree_v2.argtypes = [ctypes.c_uint64]
        self.libcuda.cuMemcpyHtoD_v2.argtypes = [ctypes.c_uint64, ctypes.c_void_p, ctypes.c_size_t]
        self.libcuda.cuMemcpyDtoH_v2.argtypes = [ctypes.c_void_p, ctypes.c_uint64, ctypes.c_size_t]
        self.libcuda.cuCtxSetLimit.argtypes = [ctypes.c_int, ctypes.c_size_t]
        self.libcuda.cuCtxGetLimit.argtypes = [ctypes.POINTER(ctypes.c_size_t), ctypes.c_int]

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
        self.libcuda.cuCtxSetCurrent.argtypes = [ctypes.c_void_p]
        self.libcuda.cuCtxCreate_v2.argtypes = [ctypes.POINTER(ctypes.c_void_p), ctypes.c_uint, ctypes.c_int]
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
        count = ctypes.c_int()
        if self.libcuda.cuDeviceGetCount(ctypes.byref(count)) != 0 or count.value < 1:
            raise CUDAExecutionError("no CUDA devices available")

    def _get_device(self, ordinal: int):
        device = ctypes.c_int()
        if self.libcuda.cuDeviceGet(ctypes.byref(device), ordinal) != 0:
            raise CUDAExecutionError("cuDeviceGet failed")
        return device

    def _create_context(self, device):
        context = ctypes.c_void_p()
        create = getattr(self.libcuda, "cuCtxCreate_v2", self.libcuda.cuCtxCreate)
        if create(ctypes.byref(context), 0, device) != 0:
            raise CUDAExecutionError("cuCtxCreate failed")
        if self.libcuda.cuCtxSetCurrent(context) != 0:
            raise CUDAExecutionError("cuCtxSetCurrent failed after create")
        return context

    def _configure_device_limits(self) -> None:
        # CU_LIMIT_STACK_SIZE=0, CU_LIMIT_MALLOC_HEAP_SIZE=2.
        # Stack caps around ~160KB on consumer GPUs; larger requests return
        # CUDA_ERROR_INVALID_VALUE. Device malloc needs an explicit heap size
        # (default ~8MB is too small for inductive ADT allocation).
        stack_bytes = 160 * 1024
        heap_bytes = 2 * 1024 * 1024 * 1024
        if self.libcuda.cuCtxSetLimit(0, stack_bytes) != 0:
            # Fall back to the largest commonly accepted size.
            for candidate in (128 * 1024, 96 * 1024, 64 * 1024):
                if self.libcuda.cuCtxSetLimit(0, candidate) == 0:
                    stack_bytes = candidate
                    break
            else:
                logger.warning("cuCtxSetLimit(STACK_SIZE) failed; deep GPU recursion may fault")
        if self.libcuda.cuCtxSetLimit(2, heap_bytes) != 0:
            for candidate in (1024, 512, 256, 128):
                if self.libcuda.cuCtxSetLimit(2, candidate * 1024 * 1024) == 0:
                    heap_bytes = candidate * 1024 * 1024
                    break
            else:
                logger.warning("cuCtxSetLimit(MALLOC_HEAP_SIZE) failed; device ADT malloc may return null")
                return
        logger.debug(f"CUDA device heap={heap_bytes} stack={stack_bytes}")

    def _cuda_error_name(self, code: int) -> str:
        get_name = getattr(self.libcuda, "cuGetErrorName", None)
        if get_name is None:
            return str(code)
        get_name.argtypes = [ctypes.c_int, ctypes.POINTER(ctypes.c_char_p)]
        get_name.restype = ctypes.c_int
        ptr = ctypes.c_char_p()
        if get_name(code, ctypes.byref(ptr)) != 0 or not ptr.value:
            return str(code)
        return ptr.value.decode("utf-8", errors="replace")

    def execute(
        self,
        llvm_ir: str,
        func_name: str,
        args: List[Any],
        arg_types: List[LLVMType],
        ret_type: LLVMType,
    ) -> Any:
        logger.debug(f"Executing kernel {func_name} on GPU.")
        if self.libcuda.cuCtxSetCurrent(self.context) != 0:
            raise CUDAExecutionError("cuCtxSetCurrent failed")
        if isinstance(ret_type, LLVMPointerType):
            raise CUDAExecutionError("GPU pointer returns require an explicit output-buffer entry point")

        ir_hash = hash(llvm_ir)
        if ir_hash not in self._module_cache:
            ptx = self._compile_to_ptx(llvm_ir)
            self._module_cache[ir_hash] = self._load_module(ptx)

        module = self._module_cache[ir_hash]
        function = self._get_function(module, func_name + "__kernel")

        device_ptrs = []
        kernel_params = []
        cleanup_tasks = []
        scalar_args = []
        result_buffer = None

        try:
            for arg, ty in zip(args, arg_types):
                if isinstance(ty, LLVMPointerType):
                    cty = self._get_ctypes_type(ty.element_type)
                    data = (cty * len(arg))(*arg)
                    size = ctypes.sizeof(data)
                    d_ptr = ctypes.c_uint64()
                    if self.libcuda.cuMemAlloc_v2(ctypes.byref(d_ptr), max(4, size)) != 0:
                        raise CUDAExecutionError("cuMemAlloc failed")
                    if self.libcuda.cuMemcpyHtoD_v2(d_ptr.value, ctypes.cast(data, ctypes.c_void_p), size) != 0:
                        raise CUDAExecutionError("cuMemcpyHtoD failed")
                    device_ptrs.append(d_ptr)
                    kernel_params.append(ctypes.addressof(d_ptr))
                    cleanup_tasks.append((d_ptr, data, size, arg))
                else:
                    c_val = self._get_ctypes_type(ty)(arg)
                    scalar_args.append(c_val)  # Keep every parameter alive until launch completes.
                    kernel_params.append(ctypes.addressof(c_val))

            if not isinstance(ret_type, LLVMVoidType):
                result_buffer = self._get_ctypes_type(ret_type)()
                result_ptr = ctypes.c_uint64()
                if self.libcuda.cuMemAlloc_v2(ctypes.byref(result_ptr), ctypes.sizeof(result_buffer)) != 0:
                    raise CUDAExecutionError("cuMemAlloc failed for result")
                device_ptrs.append(result_ptr)
                kernel_params.append(ctypes.addressof(result_ptr))

            params_ptr = (ctypes.c_void_p * len(kernel_params))(*[ctypes.c_void_p(p) for p in kernel_params])

            launch_rc = self.libcuda.cuLaunchKernel(function, 1, 1, 1, 1, 1, 1, 0, None, params_ptr, None)
            if launch_rc != 0:
                raise CUDAExecutionError(f"cuLaunchKernel failed for {func_name}: {self._cuda_error_name(launch_rc)}")

            sync_rc = self.libcuda.cuCtxSynchronize()
            if sync_rc != 0:
                raise CUDAExecutionError(
                    f"cuCtxSynchronize failed during {func_name} execution: {self._cuda_error_name(sync_rc)}"
                )

            for d_ptr, host_data, size, original_arg in cleanup_tasks:
                if self.libcuda.cuMemcpyDtoH_v2(ctypes.cast(host_data, ctypes.c_void_p), d_ptr.value, size) != 0:
                    raise CUDAExecutionError("cuMemcpyDtoH failed")
                if isinstance(original_arg, list):
                    original_arg[:] = list(host_data)

            if result_buffer is not None:
                if (
                    self.libcuda.cuMemcpyDtoH_v2(
                        ctypes.byref(result_buffer), result_ptr.value, ctypes.sizeof(result_buffer)
                    )
                    != 0
                ):
                    raise CUDAExecutionError("cuMemcpyDtoH failed for result")
                return result_buffer.value
            return None

        finally:
            for d_ptr in device_ptrs:
                self.libcuda.cuMemFree_v2(d_ptr.value if hasattr(d_ptr, "value") else d_ptr)

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
        from aeon.llvm.optimization import optimize_module

        llvm.initialize_all_targets()
        llvm.initialize_all_asmprinters()
        mod = llvm.parse_assembly(llvm_ir)
        triple = "nvptx64-nvidia-cuda"
        target = llvm.Target.from_triple(triple)
        tm = target.create_target_machine(cpu="sm_75")  # Turing+; heap malloc + recursion
        optimize_module(mod, tm)
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
            ptx_bytes = ptx.encode("utf-8") + b"\0"
            if self.libcuda.cuLinkAddData_v2(link_state, 1, ptx_bytes, len(ptx_bytes), b"aeon.ptx", 0, None, None) != 0:
                raise CUDAExecutionError("cuLinkAddData (PTX) failed")

            devrt_path = self._find_libcudadevrt()
            if devrt_path:
                with open(devrt_path, "rb") as f:
                    devrt_data = f.read()
                    if (
                        self.libcuda.cuLinkAddData_v2(
                            link_state, 4, devrt_data, len(devrt_data), b"libcudadevrt.a", 0, None, None
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
