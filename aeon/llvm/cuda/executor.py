from __future__ import annotations

import ctypes
import os
import weakref
from typing import Any, List

import llvmlite.binding as llvm
from loguru import logger
from aeon.bindings.ndarray import ArrayStorage, ManagedArray, NDArray, ReadOnlyBuffer

from aeon.llvm.core import LLVMExecutionEngine, LLVMBackendError
from aeon.llvm.llvm_ast import LLVMType, LLVMPointerType, LLVMVoidType, LLVMNDArrayType
from aeon.llvm.utils import is_array_pointer
from aeon.llvm.ndarray import pack_descriptor, descriptor_shape, finish_array
from aeon.llvm.cuda.reduction import REDUCTION_THREADS


class CUDAExecutionError(LLVMBackendError):
    pass


class DeviceArray:
    """A storage-owned allocation whose elements remain on the device between calls."""

    def __init__(self, engine, storage: ArrayStorage, ctype):
        self.engine = engine
        self.storage = weakref.ref(storage)
        self.ctype = ctype
        self.count = len(storage.host)
        self.pointer = ctypes.c_uint64()
        self.version = -1
        self.host_snapshot: tuple[Any, ...] = ()
        engine._activate()
        if engine.libcuda.cuMemAlloc_v2(ctypes.byref(self.pointer), max(4, self.count * ctypes.sizeof(ctype))) != 0:
            raise CUDAExecutionError("cuMemAlloc failed for array data")
        try:
            self.upload(storage)
        except Exception:
            self.close()
            raise

    def upload(self, storage: ArrayStorage) -> None:
        values = storage.read()
        if len(values) != self.count:
            raise ValueError("Array storage changed its element count")
        data = (self.ctype * self.count)(*values)
        self.engine._activate()
        if (
            self.engine.libcuda.cuMemcpyHtoD_v2(
                self.pointer.value, ctypes.cast(data, ctypes.c_void_p), ctypes.sizeof(data)
            )
            != 0
        ):
            raise CUDAExecutionError("cuMemcpyHtoD failed for array data")
        self.version = storage.version
        self.host_snapshot = tuple(values) if storage.exposed else ()

    def download(self, values: list[Any]) -> None:
        self.engine._activate()
        data = (self.ctype * self.count)()
        if (
            self.engine.libcuda.cuMemcpyDtoH_v2(
                ctypes.cast(data, ctypes.c_void_p), self.pointer.value, ctypes.sizeof(data)
            )
            != 0
        ):
            raise CUDAExecutionError("cuMemcpyDtoH failed for array data")
        list.__setitem__(values, slice(None), list(data))
        storage = self.storage()
        self.host_snapshot = tuple(values) if storage is not None and storage.exposed else ()

    def close(self) -> None:
        if self.pointer.value:
            previous = ctypes.c_void_p()
            get_current = getattr(self.engine.libcuda, "cuCtxGetCurrent", None)
            restore = get_current is not None and get_current(ctypes.byref(previous)) == 0
            self.engine._activate()
            try:
                if self.engine.libcuda.cuMemFree_v2(self.pointer.value) != 0:
                    raise CUDAExecutionError("cuMemFree failed for array data")
                self.pointer = ctypes.c_uint64()
            finally:
                if restore:
                    self.engine.libcuda.cuCtxSetCurrent(previous)

    def __del__(self):
        try:
            self.close()
        except Exception:
            logger.debug("Could not release device array during finalization")


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
            self._resident_arrays: weakref.WeakSet[DeviceArray] = weakref.WeakSet()
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
        get_count = self.libcuda.cuDeviceGetCount
        get_count.argtypes = [ctypes.POINTER(ctypes.c_int)]
        get_count.restype = ctypes.c_int
        if get_count(ctypes.byref(count)) != 0 or count.value < 1:
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

    def _activate(self) -> None:
        if self.libcuda.cuCtxSetCurrent(self.context) != 0:
            raise CUDAExecutionError("cuCtxSetCurrent failed")

    def _device_array(self, storage: ArrayStorage, ctype) -> DeviceArray:
        resident = storage.device
        if resident is not None and (
            resident.engine is not self or resident.ctype != ctype or resident.count != len(storage.host)
        ):
            storage.read()
            resident.close()
            storage.device = None
            resident = None
        if resident is None:
            resident = DeviceArray(self, storage, ctype)
            storage.device = resident
            if not hasattr(self, "_resident_arrays"):
                self._resident_arrays = weakref.WeakSet()
            self._resident_arrays.add(resident)
        else:
            if storage.exposed and storage.host_current and tuple(storage.host) != resident.host_snapshot:
                storage.version += 1
            if resident.version != storage.version:
                try:
                    resident.upload(storage)
                except Exception:
                    resident.close()
                    storage.device = None
                    raise
        self._activate()
        return resident

    def close(self) -> None:
        """Materialize live arrays before releasing this engine's resident buffers."""
        for resident in list(getattr(self, "_resident_arrays", ())):
            storage = resident.storage()
            if storage is not None and storage.device is resident:
                storage.read()
                storage.device = None
            resident.close()

    def execute(
        self,
        llvm_ir: str,
        func_name: str,
        args: List[Any],
        arg_types: List[LLVMType],
        ret_type: LLVMType,
        launch_shape: tuple[int, ...] | None = None,
        reduction_count: int | None = None,
    ) -> Any:
        logger.debug(f"Executing kernel {func_name} on GPU.")
        self._activate()
        returns_ndarray = isinstance(ret_type, LLVMNDArrayType)
        returns_array = isinstance(ret_type, (LLVMPointerType, LLVMNDArrayType))
        if reduction_count is not None:
            if not 0 <= reduction_count <= 2**31 - 1 or returns_array or isinstance(ret_type, LLVMVoidType):
                raise ValueError("Parallel reduction requires a valid length and scalar result")
            launch_shape = (reduction_count,)
        array_element_type = ret_type.element_type if isinstance(ret_type, (LLVMPointerType, LLVMNDArrayType)) else None
        if returns_array and (
            not (is_array_pointer(ret_type) or returns_ndarray)
            or not any(
                ty.element_type == array_element_type
                and (
                    (returns_ndarray and isinstance(ty, LLVMNDArrayType))
                    or (
                        not returns_ndarray
                        and isinstance(ty, LLVMPointerType)
                        and isinstance(arg, (list, ReadOnlyBuffer))
                    )
                )
                for arg, ty in zip(args, arg_types)
                if isinstance(ty, (LLVMPointerType, LLVMNDArrayType))
            )
        ):
            raise CUDAExecutionError("GPU array returns must refer to an array passed as a parameter")

        ir_hash = hash(llvm_ir)
        if ir_hash not in self._module_cache:
            ptx = self._compile_to_ptx(llvm_ir)
            self._module_cache[ir_hash] = self._load_module(ptx)

        module = self._module_cache[ir_hash]
        function = self._get_function(module, func_name + "__kernel")

        device_ptrs = []
        kernel_params = []
        cleanup_tasks = []
        array_results: dict[int, Any] = {}
        ndarray_tasks = {}
        resident_tasks: dict[ArrayStorage, DeviceArray] = {}
        scalar_args = []
        result_buffer = None
        launched = False

        try:
            for arg, ty in zip(args, arg_types):
                if isinstance(ty, LLVMNDArrayType):
                    if not isinstance(arg, NDArray) or arg.rank != ty.rank:
                        raise ValueError(f"Expected a rank-{ty.rank} NDArray")
                    descriptor = pack_descriptor(arg, 0)
                    storage = arg._storage
                    ctype = self._get_ctypes_type(ty.element_type)
                    if storage in resident_tasks and resident_tasks[storage].ctype != ctype:
                        raise CUDAExecutionError("Aliased array arguments must have the same element type")
                    resident = self._device_array(storage, ctype)
                    resident_tasks[storage] = resident
                    descriptor.data = resident.pointer.value
                    descriptor_ptr = ctypes.c_uint64()
                    if self.libcuda.cuMemAlloc_v2(ctypes.byref(descriptor_ptr), ctypes.sizeof(descriptor)) != 0:
                        raise CUDAExecutionError("cuMemAlloc failed for NDArray descriptor")
                    device_ptrs.append(descriptor_ptr)
                    if (
                        self.libcuda.cuMemcpyHtoD_v2(
                            descriptor_ptr.value, ctypes.byref(descriptor), ctypes.sizeof(descriptor)
                        )
                        != 0
                    ):
                        raise CUDAExecutionError("cuMemcpyHtoD failed for NDArray descriptor")
                    kernel_params.append(ctypes.addressof(descriptor_ptr))
                    ndarray_tasks[descriptor_ptr.value] = (arg, descriptor, resident.pointer.value, ty)
                    if returns_ndarray and ty.element_type == array_element_type:
                        array_results[descriptor_ptr.value] = arg
                elif isinstance(ty, LLVMPointerType) and isinstance(arg, (ReadOnlyBuffer, ManagedArray)):
                    storage = arg._storage
                    ctype = self._get_ctypes_type(ty.element_type)
                    if storage in resident_tasks and resident_tasks[storage].ctype != ctype:
                        raise CUDAExecutionError("Aliased array arguments must have the same element type")
                    resident = self._device_array(storage, ctype)
                    resident_tasks[storage] = resident
                    kernel_params.append(ctypes.addressof(resident.pointer))
                    if isinstance(ret_type, LLVMPointerType) and ty.element_type == array_element_type:
                        array_results[resident.pointer.value] = arg
                elif isinstance(ty, LLVMPointerType):
                    cty = self._get_ctypes_type(ty.element_type)
                    data = (cty * len(arg))(*arg)
                    size = ctypes.sizeof(data)
                    d_ptr = ctypes.c_uint64()
                    if self.libcuda.cuMemAlloc_v2(ctypes.byref(d_ptr), max(4, size)) != 0:
                        raise CUDAExecutionError("cuMemAlloc failed")
                    device_ptrs.append(d_ptr)
                    if self.libcuda.cuMemcpyHtoD_v2(d_ptr.value, ctypes.cast(data, ctypes.c_void_p), size) != 0:
                        raise CUDAExecutionError("cuMemcpyHtoD failed")
                    kernel_params.append(ctypes.addressof(d_ptr))
                    cleanup_tasks.append((d_ptr, data, size, arg))
                    if (
                        isinstance(ret_type, LLVMPointerType)
                        and ty.element_type == array_element_type
                        and isinstance(arg, list)
                    ):
                        array_results[d_ptr.value] = arg
                else:
                    c_val = self._get_ctypes_type(ty)(arg)
                    scalar_args.append(c_val)  # Keep every parameter alive until launch completes.
                    kernel_params.append(ctypes.addressof(c_val))

            if not isinstance(ret_type, LLVMVoidType):
                result_buffer = ctypes.c_uint64() if returns_array else self._get_ctypes_type(ret_type)()
                result_ptr = ctypes.c_uint64()
                result_count = (
                    max(1, (reduction_count + REDUCTION_THREADS - 1) // REDUCTION_THREADS)
                    if reduction_count is not None
                    else 1
                )
                if (
                    self.libcuda.cuMemAlloc_v2(ctypes.byref(result_ptr), result_count * ctypes.sizeof(result_buffer))
                    != 0
                ):
                    raise CUDAExecutionError("cuMemAlloc failed for result")
                device_ptrs.append(result_ptr)
                kernel_params.append(ctypes.addressof(result_ptr))
                if reduction_count is not None and result_count > 1:
                    other = ctypes.c_uint64()
                    if (
                        self.libcuda.cuMemAlloc_v2(ctypes.byref(other), result_count * ctypes.sizeof(result_buffer))
                        != 0
                    ):
                        raise CUDAExecutionError("cuMemAlloc failed for reduction scratch")
                    device_ptrs.append(other)

            params_ptr = (ctypes.c_void_p * len(kernel_params))(*[ctypes.c_void_p(p) for p in kernel_params])

            grid, block = self._launch_dimensions(launch_shape)
            launch_rc = self.libcuda.cuLaunchKernel(function, *grid, *block, 0, None, params_ptr, None)
            if launch_rc != 0:
                raise CUDAExecutionError(f"cuLaunchKernel failed for {func_name}: {self._cuda_error_name(launch_rc)}")
            launched = True

            if reduction_count is not None and result_count > 1:
                # Default-stream ordering supplies the barrier between passes.
                # Partial arrays never cross the PCIe boundary.
                continuation = self._get_function(module, func_name + "__reduce")
                remaining = result_count
                while remaining > 1:
                    pass_count = ctypes.c_int32(remaining)
                    scalar_args.append(pass_count)
                    pass_params = kernel_params[:-1] + [
                        ctypes.addressof(result_ptr),
                        ctypes.addressof(pass_count),
                        ctypes.addressof(other),
                    ]
                    pass_ptr = (ctypes.c_void_p * len(pass_params))(*pass_params)
                    grid, block = self._launch_dimensions((remaining,))
                    rc = self.libcuda.cuLaunchKernel(continuation, *grid, *block, 0, None, pass_ptr, None)
                    if rc != 0:
                        raise CUDAExecutionError(
                            f"cuLaunchKernel failed for reduction pass: {self._cuda_error_name(rc)}"
                        )
                    remaining = (remaining + REDUCTION_THREADS - 1) // REDUCTION_THREADS
                    result_ptr, other = other, result_ptr

            if reduction_count is None:
                for storage in resident_tasks:
                    storage.host_current = False

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

            shapes = {}
            for address, (arg, descriptor, data_address, ty) in ndarray_tasks.items():
                if self.libcuda.cuMemcpyDtoH_v2(ctypes.byref(descriptor), address, ctypes.sizeof(descriptor)) != 0:
                    raise CUDAExecutionError("cuMemcpyDtoH failed for NDArray descriptor")
                shapes[address] = descriptor_shape(descriptor, arg, data_address)

            # Raw host lists can outlive a .data access. Preserve their ordinary
            # Python alias semantics, while retaining the allocation for reuse.
            for storage in resident_tasks:
                if storage.exposed:
                    storage.read()

            if result_buffer is not None:
                if (
                    self.libcuda.cuMemcpyDtoH_v2(
                        ctypes.byref(result_buffer), result_ptr.value, ctypes.sizeof(result_buffer)
                    )
                    != 0
                ):
                    raise CUDAExecutionError("cuMemcpyDtoH failed for result")
                if returns_array:
                    if result_buffer.value not in array_results:
                        raise CUDAExecutionError("GPU array result does not refer to an array passed as a parameter")
                    if isinstance(ret_type, LLVMNDArrayType):
                        return finish_array(array_results[result_buffer.value], shapes[result_buffer.value], ret_type)
                    return array_results[result_buffer.value]
                return result_buffer.value
            return None

        except Exception as error:
            for storage, resident in resident_tasks.items():
                try:
                    if launched:
                        storage.host_current = False
                    storage.read()
                except Exception:
                    storage.failure = error
                finally:
                    storage.device = None
                    try:
                        resident.close()
                    except Exception:
                        logger.debug("Could not release array after CUDA failure")
            raise
        finally:
            for d_ptr in device_ptrs:
                self.libcuda.cuMemFree_v2(d_ptr.value if hasattr(d_ptr, "value") else d_ptr)

    @staticmethod
    def _launch_dimensions(shape):
        if shape is None:
            return (1, 1, 1), (1, 1, 1)
        # Empty arrays still launch one block to return their descriptor.
        block = {1: (256, 1, 1), 2: (16, 16, 1), 3: (8, 8, 4)}[len(shape)]
        if any(n == 0 for n in shape):
            return (1, 1, 1), block
        extents = tuple(reversed(shape)) + (1,) * (3 - len(shape))
        grid = tuple(max(1, (n + threads - 1) // threads) for n, threads in zip(extents, block))
        # CUDA's y/z grid bounds are 65535; x also accommodates Int extents.
        if grid[1] > 65535 or grid[2] > 65535:
            raise CUDAExecutionError("NDArray shape exceeds the CUDA y/z grid limits")
        return grid, block

    def _get_ctypes_type(self, ty: LLVMType):
        from aeon.llvm.llvm_ast import LLVMIntType, LLVMFloatType, LLVMDoubleType, LLVMBoolType

        if isinstance(ty, LLVMIntType):
            integer_types = {
                1: ctypes.c_bool,
                8: ctypes.c_int8,
                16: ctypes.c_int16,
                32: ctypes.c_int32,
                64: ctypes.c_int64,
            }
            if ty.bits not in integer_types:
                raise CUDAExecutionError(f"unsupported integer width: {ty.bits} bits")
            return integer_types[ty.bits]
        mapping = {
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
