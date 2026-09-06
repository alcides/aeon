"""Small, dependency-free binding to the CUDA Driver API.

Importing this module does not load CUDA.  The driver is discovered and
initialised only when :func:`device` (or another operation which needs a
``Device``) is called.  This is intentional: Aeon must remain usable on
machines without an NVIDIA driver.

The public objects model the lifetime used by ``Cuda.ae``: uploads produce a
ready :class:`Buffer`, a kernel launch produces :class:`Pending`, and
``synchronize`` turns that pending result into a ready buffer.  Downloads copy
to fresh host arrays while preserving the ready buffer for subsequent downloads
or an explicit ``free``.  ``free`` and ``discard`` are idempotent so error paths
and finalizers can safely clean up.
"""

from __future__ import annotations

import array
import ctypes
import ctypes.util
import math
import sys
import threading
import weakref
from dataclasses import dataclass
from typing import Any, Iterable, Literal, cast

_DType = Literal["i32", "float64"]
_ITEM_SIZE: dict[_DType, int] = {"i32": 4, "float64": 8}
_KERNEL_NAME: dict[_DType, bytes] = {"i32": b"aeon_vector_add_i32", "float64": b"aeon_vector_add_float64"}

# Memory kinds (refinement measures / Aeon natives).
MEM_KIND_DEVICE = 0
MEM_KIND_HOST_PINNED = 1
MEM_KIND_MANAGED = 2
MEM_KIND_HOST = 3

# Access modes.
ACCESS_READ_ONLY = 0
ACCESS_READ_WRITE = 1

# CUDA driver attribute indices used below.
_CU_DEVICE_ATTRIBUTE_MAX_THREADS_PER_BLOCK = 1
_CU_DEVICE_ATTRIBUTE_MAX_SHARED_MEMORY_PER_BLOCK = 8
_CU_DEVICE_ATTRIBUTE_WARP_SIZE = 10

# Architectural defaults used when validating without a live device.
_DEFAULT_WARP_SIZE = 32
_MAX_THREADS_PER_BLOCK = 1024


class CUDAError(RuntimeError):
    """Base exception for CUDA binding failures."""


class CUDAUnavailableError(CUDAError):
    """Raised when the CUDA driver or a CUDA device is unavailable."""


class CUDAStateError(CUDAError):
    """Raised when a consumed CUDA handle is used again."""


class _CudaDriver:
    """Typed, lazy facade over ``libcuda``."""

    def __init__(self) -> None:
        self.lib = self._open_library()
        self._bind_functions()
        self._initialised = False
        self._init_lock = threading.Lock()

    @staticmethod
    def _open_library() -> ctypes.CDLL:
        candidates: list[str] = []
        found = ctypes.util.find_library("cuda")
        if found:
            candidates.append(found)
        if sys.platform == "win32":
            candidates.extend(["nvcuda.dll"])
        elif sys.platform == "darwin":
            candidates.extend(["libcuda.dylib"])
        else:
            candidates.extend(["libcuda.so.1", "libcuda.so"])

        errors: list[str] = []
        for candidate in dict.fromkeys(candidates):
            try:
                return ctypes.CDLL(candidate)
            except OSError as exc:
                errors.append(str(exc))
        detail = f" ({'; '.join(errors)})" if errors else ""
        raise CUDAUnavailableError(f"CUDA driver library was not found{detail}")

    def _symbol(self, name: str, *fallbacks: str) -> Any:
        for candidate in (name, *fallbacks):
            try:
                return getattr(self.lib, candidate)
            except AttributeError:
                pass
        raise CUDAUnavailableError(f"CUDA driver does not provide {name}")

    @staticmethod
    def _configure(fn: Any, argtypes: list[Any]) -> Any:
        fn.argtypes = argtypes
        fn.restype = ctypes.c_int
        return fn

    def _bind_functions(self) -> None:
        void_p = ctypes.c_void_p
        uint = ctypes.c_uint
        size_t = ctypes.c_size_t
        int_p = ctypes.POINTER(ctypes.c_int)
        void_pp = ctypes.POINTER(void_p)

        self.cuInit = self._configure(self._symbol("cuInit"), [uint])
        self.cuDeviceGetCount = self._configure(self._symbol("cuDeviceGetCount"), [int_p])
        self.cuDeviceGet = self._configure(self._symbol("cuDeviceGet"), [int_p, ctypes.c_int])
        self.cuDeviceGetName = self._configure(
            self._symbol("cuDeviceGetName"), [ctypes.POINTER(ctypes.c_char), ctypes.c_int, ctypes.c_int]
        )
        self.cuDeviceComputeCapability = self._configure(
            self._symbol("cuDeviceComputeCapability"), [int_p, int_p, ctypes.c_int]
        )
        self.cuDeviceGetAttribute = self._configure(
            self._symbol("cuDeviceGetAttribute"), [int_p, ctypes.c_int, ctypes.c_int]
        )
        self.cuDeviceTotalMem = self._configure(
            self._symbol("cuDeviceTotalMem_v2", "cuDeviceTotalMem"), [ctypes.POINTER(ctypes.c_size_t), ctypes.c_int]
        )
        self.cuCtxCreate = self._configure(self._symbol("cuCtxCreate_v2", "cuCtxCreate"), [void_pp, uint, ctypes.c_int])
        self.cuCtxDestroy = self._configure(self._symbol("cuCtxDestroy_v2", "cuCtxDestroy"), [void_p])
        self.cuCtxSetCurrent = self._configure(self._symbol("cuCtxSetCurrent"), [void_p])
        self.cuCtxSynchronize = self._configure(self._symbol("cuCtxSynchronize"), [])
        self.cuStreamCreate = self._configure(self._symbol("cuStreamCreate"), [ctypes.POINTER(ctypes.c_void_p), uint])
        self.cuStreamDestroy = self._configure(self._symbol("cuStreamDestroy"), [ctypes.c_void_p])
        self.cuStreamSynchronize = self._configure(self._symbol("cuStreamSynchronize"), [ctypes.c_void_p])
        self.cuMemAlloc = self._configure(
            self._symbol("cuMemAlloc_v2", "cuMemAlloc"), [ctypes.POINTER(ctypes.c_uint64), size_t]
        )
        self.cuMemFree = self._configure(self._symbol("cuMemFree_v2", "cuMemFree"), [ctypes.c_uint64])
        self.cuMemcpyHtoD = self._configure(
            self._symbol("cuMemcpyHtoD_v2", "cuMemcpyHtoD"), [ctypes.c_uint64, void_p, size_t]
        )
        self.cuMemcpyDtoH = self._configure(
            self._symbol("cuMemcpyDtoH_v2", "cuMemcpyDtoH"), [void_p, ctypes.c_uint64, size_t]
        )
        self.cuModuleLoadData = self._configure(self._symbol("cuModuleLoadData"), [void_pp, void_p])
        self.cuModuleUnload = self._configure(self._symbol("cuModuleUnload"), [void_p])
        self.cuModuleGetFunction = self._configure(
            self._symbol("cuModuleGetFunction"), [void_pp, void_p, ctypes.c_char_p]
        )
        self.cuLaunchKernel = self._configure(
            self._symbol("cuLaunchKernel"),
            [
                void_p,
                uint,
                uint,
                uint,
                uint,
                uint,
                uint,
                uint,
                void_p,
                void_pp,
                void_pp,
            ],
        )
        try:
            self.cuGetErrorName = self._configure(
                self._symbol("cuGetErrorName"), [ctypes.c_int, ctypes.POINTER(ctypes.c_char_p)]
            )
            self.cuGetErrorString = self._configure(
                self._symbol("cuGetErrorString"), [ctypes.c_int, ctypes.POINTER(ctypes.c_char_p)]
            )
        except CUDAUnavailableError:
            self.cuGetErrorName = None
            self.cuGetErrorString = None

    def initialise(self) -> None:
        with self._init_lock:
            if not self._initialised:
                self.check(self.cuInit(0), "cuInit")
                self._initialised = True

    def error_text(self, result: int) -> str:
        details: list[str] = []
        for fn in (self.cuGetErrorName, self.cuGetErrorString):
            if fn is None:
                continue
            text = ctypes.c_char_p()
            if fn(result, ctypes.byref(text)) == 0 and text.value:
                details.append(text.value.decode("utf-8", errors="replace"))
        return ": ".join(details) if details else f"CUDA error {result}"

    def check(self, result: int, operation: str) -> None:
        if result != 0:
            raise CUDAError(f"{operation} failed: {self.error_text(result)}")


_DRIVER: _CudaDriver | None = None
_DRIVER_LOCK = threading.Lock()


def _driver() -> _CudaDriver:
    global _DRIVER
    with _DRIVER_LOCK:
        if _DRIVER is None:
            _DRIVER = _CudaDriver()
        driver = _DRIVER
    driver.initialise()
    return driver


class Device:
    """An owned CUDA context for one physical device."""

    def __init__(self, ordinal: int = 0) -> None:
        if isinstance(ordinal, bool) or not isinstance(ordinal, int) or ordinal < 0:
            raise ValueError("CUDA device ordinal must be a non-negative integer")
        driver = _driver()
        count = ctypes.c_int()
        driver.check(driver.cuDeviceGetCount(ctypes.byref(count)), "cuDeviceGetCount")
        if ordinal >= count.value:
            raise CUDAUnavailableError(f"CUDA device {ordinal} is unavailable (found {count.value})")

        handle = ctypes.c_int()
        driver.check(driver.cuDeviceGet(ctypes.byref(handle), ordinal), "cuDeviceGet")
        context = ctypes.c_void_p()
        driver.check(driver.cuCtxCreate(ctypes.byref(context), 0, handle.value), "cuCtxCreate")

        self.ordinal = ordinal
        # These attributes are the runtime counterparts of Cuda.ae's measures.
        self.device_id = ordinal
        self._driver = driver
        self._handle = handle.value
        self._context = context
        self._closed = False
        self._buffers: weakref.WeakSet[Buffer] = weakref.WeakSet()
        self._pending: weakref.WeakSet[Pending] = weakref.WeakSet()
        self._streams: weakref.WeakSet[Stream] = weakref.WeakSet()
        self._module: ctypes.c_void_p | None = None
        self._functions: dict[_DType, ctypes.c_void_p] = {}
        self._lock = threading.RLock()

        try:
            name = ctypes.create_string_buffer(256)
            driver.check(driver.cuDeviceGetName(name, len(name), handle.value), "cuDeviceGetName")
            self.name = name.value.decode("utf-8", errors="replace")
            major, minor = ctypes.c_int(), ctypes.c_int()
            driver.check(
                driver.cuDeviceComputeCapability(ctypes.byref(major), ctypes.byref(minor), handle.value),
                "cuDeviceComputeCapability",
            )
            self.compute_capability = (major.value, minor.value)
            max_threads = ctypes.c_int()
            driver.check(
                driver.cuDeviceGetAttribute(
                    ctypes.byref(max_threads), _CU_DEVICE_ATTRIBUTE_MAX_THREADS_PER_BLOCK, handle.value
                ),
                "cuDeviceGetAttribute",
            )
            self.max_threads_per_block = max_threads.value
            max_shared = ctypes.c_int()
            driver.check(
                driver.cuDeviceGetAttribute(
                    ctypes.byref(max_shared), _CU_DEVICE_ATTRIBUTE_MAX_SHARED_MEMORY_PER_BLOCK, handle.value
                ),
                "cuDeviceGetAttribute",
            )
            self.max_shared_mem_per_block = max_shared.value
            warp = ctypes.c_int()
            driver.check(
                driver.cuDeviceGetAttribute(ctypes.byref(warp), _CU_DEVICE_ATTRIBUTE_WARP_SIZE, handle.value),
                "cuDeviceGetAttribute",
            )
            self.warp_size = warp.value
            total_mem = ctypes.c_size_t()
            driver.check(
                driver.cuDeviceTotalMem(ctypes.byref(total_mem), handle.value),
                "cuDeviceTotalMem",
            )
            self.max_allocation = total_mem.value
        except BaseException:
            try:
                driver.cuCtxDestroy(context)
            finally:
                self._closed = True
            raise

    def _ensure_open(self) -> None:
        if self._closed:
            raise CUDAStateError("CUDA device is closed")

    def _activate(self) -> None:
        self._ensure_open()
        self._driver.check(self._driver.cuCtxSetCurrent(self._context), "cuCtxSetCurrent")

    def _register_buffer(self, buffer: Buffer) -> None:
        self._buffers.add(buffer)

    def _function(self, dtype: _DType) -> ctypes.c_void_p:
        self._activate()
        if dtype in self._functions:
            return self._functions[dtype]
        if self._module is None:
            ptx = _compile_vector_add_ptx(self.compute_capability)
            ptx_data = ctypes.create_string_buffer(ptx.encode("utf-8"))
            module = ctypes.c_void_p()
            self._driver.check(
                self._driver.cuModuleLoadData(ctypes.byref(module), ctypes.cast(ptx_data, ctypes.c_void_p)),
                "cuModuleLoadData",
            )
            self._module = module
        function = ctypes.c_void_p()
        self._driver.check(
            self._driver.cuModuleGetFunction(ctypes.byref(function), self._module, _KERNEL_NAME[dtype]),
            "cuModuleGetFunction",
        )
        self._functions[dtype] = function
        return function

    def synchronize(self) -> None:
        with self._lock:
            self._activate()
            self._driver.check(self._driver.cuCtxSynchronize(), "cuCtxSynchronize")

    def close(self) -> None:
        """Synchronize, release children and destroy this context.

        Cleanup is best-effort but the first CUDA error is re-raised after all
        resources have had a chance to be released.
        """
        with self._lock:
            if self._closed:
                return
            error: BaseException | None = None
            try:
                self._activate()
                self._driver.check(self._driver.cuCtxSynchronize(), "cuCtxSynchronize")
            except BaseException as exc:
                error = exc
            for pending in list(self._pending):
                try:
                    pending._discard_after_device_sync()
                except BaseException as exc:
                    error = error or exc
            for stream in list(self._streams):
                try:
                    stream.close()
                except BaseException as exc:
                    error = error or exc
            for buffer in list(self._buffers):
                try:
                    buffer._free_from_device()
                except BaseException as exc:
                    error = error or exc
            if self._module is not None:
                try:
                    self._driver.check(self._driver.cuModuleUnload(self._module), "cuModuleUnload")
                except BaseException as exc:
                    error = error or exc
                self._module = None
                self._functions.clear()
            try:
                self._driver.check(self._driver.cuCtxDestroy(self._context), "cuCtxDestroy")
            except BaseException as exc:
                error = error or exc
            self._closed = True
            if error is not None:
                raise error

    def __enter__(self) -> Device:
        self._ensure_open()
        return self

    def __exit__(self, exc_type: Any, exc: Any, traceback: Any) -> None:
        self.close()

    def __del__(self) -> None:
        try:
            self.close()
        except Exception:
            pass


@dataclass(frozen=True)
class Launch1D:
    """Validated one-dimensional launch geometry."""

    size: int
    block_size: int = 256
    shared_bytes: int = 0
    require_warp_multiple: bool = False

    def __post_init__(self) -> None:
        if isinstance(self.size, bool) or not isinstance(self.size, int) or self.size <= 0:
            raise ValueError("launch size must be a positive integer")
        if isinstance(self.block_size, bool) or not isinstance(self.block_size, int) or self.block_size <= 0:
            raise ValueError("block size must be a positive integer")
        if self.block_size > self.size:
            raise ValueError("block size cannot exceed launch size")
        if self.block_size > _MAX_THREADS_PER_BLOCK:
            raise ValueError("block size cannot exceed CUDA's architectural limit of 1024")
        if isinstance(self.shared_bytes, bool) or not isinstance(self.shared_bytes, int) or self.shared_bytes < 0:
            raise ValueError("shared_bytes must be a non-negative integer")
        if not isinstance(self.require_warp_multiple, bool):
            raise ValueError("require_warp_multiple must be a bool")

    @property
    def grid_size(self) -> int:
        return math.ceil(self.size / self.block_size)


@dataclass(frozen=True)
class Launch2D:
    """Validated two-dimensional launch geometry."""

    width: int
    height: int
    block_x: int
    block_y: int
    shared_bytes: int = 0

    def __post_init__(self) -> None:
        for name, value in (
            ("width", self.width),
            ("height", self.height),
            ("block_x", self.block_x),
            ("block_y", self.block_y),
        ):
            if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
                raise ValueError(f"launch {name} must be a positive integer")
        if self.block_x * self.block_y > _MAX_THREADS_PER_BLOCK:
            raise ValueError("block_x * block_y cannot exceed CUDA's architectural limit of 1024")
        if isinstance(self.shared_bytes, bool) or not isinstance(self.shared_bytes, int) or self.shared_bytes < 0:
            raise ValueError("shared_bytes must be a non-negative integer")

    @property
    def grid_x(self) -> int:
        return math.ceil(self.width / self.block_x)

    @property
    def grid_y(self) -> int:
        return math.ceil(self.height / self.block_y)


class Stream:
    """A CUDA stream owned by one device context."""

    def __init__(self, device: Device, *, owned: bool, handle: int) -> None:
        self.device = device
        self._handle = handle
        self._owned = owned
        self._closed = False
        device._streams.add(self)

    @property
    def stream_id(self) -> int:
        return self._handle

    def _ensure_open(self) -> None:
        self.device._ensure_open()
        if self._closed:
            raise CUDAStateError("CUDA stream is closed")

    def synchronize(self) -> None:
        with self.device._lock:
            self._ensure_open()
            self.device._activate()
            if self._handle:
                self.device._driver.check(
                    self.device._driver.cuStreamSynchronize(ctypes.c_void_p(self._handle)),
                    "cuStreamSynchronize",
                )
            else:
                self.device._driver.check(self.device._driver.cuCtxSynchronize(), "cuCtxSynchronize")

    def close(self) -> None:
        with self.device._lock:
            if self._closed or not self._owned or not self._handle:
                self._closed = True
                return
            self.device._activate()
            self.device._driver.check(
                self.device._driver.cuStreamDestroy(ctypes.c_void_p(self._handle)),
                "cuStreamDestroy",
            )
            self._closed = True

    def __del__(self) -> None:
        try:
            self.close()
        except Exception:
            pass


class Buffer:
    """A ready, typed device allocation."""

    def __init__(
        self,
        device: Device,
        pointer: int,
        length: int,
        dtype: _DType,
        *,
        mem_kind: int = MEM_KIND_DEVICE,
        access: int = ACCESS_READ_WRITE,
        extent_x: int | None = None,
        extent_y: int = 1,
    ) -> None:
        if mem_kind not in (MEM_KIND_DEVICE, MEM_KIND_HOST_PINNED, MEM_KIND_MANAGED, MEM_KIND_HOST):
            raise ValueError(f"unsupported mem_kind: {mem_kind}")
        if access not in (ACCESS_READ_ONLY, ACCESS_READ_WRITE):
            raise ValueError(f"unsupported access mode: {access}")
        if extent_x is None:
            extent_x = length
        if isinstance(extent_x, bool) or not isinstance(extent_x, int) or extent_x <= 0:
            raise ValueError("extent_x must be a positive integer")
        if isinstance(extent_y, bool) or not isinstance(extent_y, int) or extent_y <= 0:
            raise ValueError("extent_y must be a positive integer")
        self.device = device
        self.pointer = pointer
        self.length = length
        self.dtype = dtype
        self.mem_kind = mem_kind
        self.access = access
        self.extent_x = extent_x
        self.extent_y = extent_y
        # Ownership transfer (e.g. as_read_only): mark ready-state consumed without cuMemFree.
        self._transferred = False
        self._freed = False
        device._register_buffer(self)

    def _ensure_ready(self) -> None:
        self.device._ensure_open()
        if self._freed or self._transferred:
            raise CUDAStateError("CUDA buffer has been freed")

    def _free_from_device(self) -> None:
        if self._freed or self._transferred:
            return
        self.device._driver.check(self.device._driver.cuMemFree(self.pointer), "cuMemFree")
        self._freed = True

    def free(self) -> None:
        with self.device._lock:
            if self._freed or self._transferred:
                self._freed = True
                return
            self.device._activate()
            self._free_from_device()

    def __len__(self) -> int:
        return self.length

    def __getitem__(self, index: int) -> int:
        """Expose refinement measures to the Aeon runtime."""
        if index == 0:
            return self.device.ordinal
        if index == 1:
            return self.length
        raise IndexError(index)

    def __enter__(self) -> Buffer:
        self._ensure_ready()
        return self

    def __exit__(self, exc_type: Any, exc: Any, traceback: Any) -> None:
        self.free()

    def __del__(self) -> None:
        try:
            self.free()
        except Exception:
            pass


class Pending:
    """The not-yet-synchronized output of an asynchronous kernel launch."""

    def __init__(self, output: Buffer, inputs: tuple[Buffer, ...], stream: Stream) -> None:
        self.device = output.device
        self.stream = stream
        self._output: Buffer | None = output
        self._inputs = inputs
        self._consumed = False
        self.device._pending.add(self)

    def _ensure_pending(self) -> Buffer:
        self.device._ensure_open()
        self.stream._ensure_open()
        if self._consumed or self._output is None:
            raise CUDAStateError("CUDA pending result has already been consumed")
        return self._output

    def synchronize(self) -> Buffer:
        with self.device._lock:
            output = self._ensure_pending()
            self.stream.synchronize()
            inputs = self._inputs
            self._consumed = True
            self._output = None
            self._inputs = ()
            try:
                for buffer in inputs:
                    buffer._free_from_device()
            except BaseException:
                # Ownership of every input and the output moved into Pending.
                # If cleanup fails, do not expose a half-cleaned result.
                for buffer in inputs:
                    try:
                        buffer._free_from_device()
                    except Exception:
                        pass
                try:
                    output._free_from_device()
                except Exception:
                    pass
                raise
            return output

    def _discard_after_device_sync(self) -> None:
        if self._consumed:
            return
        buffers = (*self._inputs, self._output) if self._output is not None else self._inputs
        self._consumed = True
        self._output = None
        self._inputs = ()
        error: BaseException | None = None
        for buffer in buffers:
            try:
                buffer._free_from_device()
            except BaseException as exc:
                error = error or exc
        if error is not None:
            raise error

    def discard(self) -> None:
        with self.device._lock:
            if self._consumed:
                return
            self.device.synchronize()
            self._discard_after_device_sync()

    def __del__(self) -> None:
        try:
            self.discard()
        except Exception:
            pass


class Status:
    """Linear-style completion token that must be checked or discarded."""

    def __init__(self, ok: bool, code: int = 0, message: str = "") -> None:
        self.ok = ok
        self.code = code
        self.message = message
        self._consumed = False

    def _ensure_live(self) -> None:
        if self._consumed:
            raise CUDAStateError("CUDA status has already been consumed")


@dataclass(frozen=True, slots=True)
class StatusBuffer:
    """Pair of a status token and an optional ready buffer (both must be handled)."""

    status: Status
    buffer: Buffer | None


def device(ordinal: int = 0) -> Device:
    return Device(ordinal)


def num_devices() -> int:
    """Return the number of visible CUDA devices without creating a context."""
    driver = _driver()
    count = ctypes.c_int()
    driver.check(driver.cuDeviceGetCount(ctypes.byref(count)), "cuDeviceGetCount")
    if count.value <= 0:
        raise CUDAUnavailableError("no CUDA devices are available")
    return count.value


def default_stream(device_: Device) -> Stream:
    return Stream(device_, owned=False, handle=0)


def create_stream(device_: Device) -> Stream:
    with device_._lock:
        device_._activate()
        stream = ctypes.c_void_p()
        device_._driver.check(device_._driver.cuStreamCreate(ctypes.byref(stream), 0), "cuStreamCreate")
    return Stream(device_, owned=True, handle=stream.value or 0)


def stream_device(stream: Stream) -> int:
    return stream.device.ordinal


def stream_id(stream: Stream) -> int:
    return stream.stream_id


def pending_stream(pending: Pending) -> int:
    return pending.stream.stream_id


def launch_1d(size: int, block_size: int | None = None, shared_bytes: int = 0) -> Launch1D:
    return Launch1D(size, min(256, size) if block_size is None else block_size, shared_bytes=shared_bytes)


def launch_1d_warped(size: int, block_size: int | None = None, shared_bytes: int = 0) -> Launch1D:
    """Build a Launch1D that must be a multiple of the device warp size at launch.

    Without a live device, construction uses the architectural default warp size
    (32): ``block_size`` must be a multiple of 32, or the whole launch must fit
    in one warp (``size <= 32``). Device-side validation uses ``device.warp_size``
    when ``require_warp_multiple`` is true.
    """
    resolved = min(256, size) if block_size is None else block_size
    if size > _DEFAULT_WARP_SIZE and resolved % _DEFAULT_WARP_SIZE != 0:
        raise ValueError(
            f"warped launch block size {resolved} must be a multiple of {_DEFAULT_WARP_SIZE} "
            f"when size ({size}) exceeds one warp"
        )
    return Launch1D(size, resolved, shared_bytes=shared_bytes, require_warp_multiple=True)


def launch_2d(width: int, height: int, block_x: int, block_y: int, shared_bytes: int = 0) -> Launch2D:
    return Launch2D(width, height, block_x, block_y, shared_bytes=shared_bytes)


def device_id(device_: Device) -> int:
    return device_.ordinal


def max_threads_per_block(device_: Device) -> int:
    return device_.max_threads_per_block


def max_shared_mem_per_block(device_: Device) -> int:
    return device_.max_shared_mem_per_block


def warp_size(device_: Device) -> int:
    return device_.warp_size


def launch_device(launch: Launch1D | tuple[Launch1D, Device]) -> int:
    if isinstance(launch, tuple):
        return launch[1].ordinal
    raise ValueError("a Launch1D descriptor alone does not own a device")


def launch_items(launch: Launch1D | tuple[Launch1D, Device]) -> int:
    return launch[0].size if isinstance(launch, tuple) else launch.size


def launch_threads(launch: Launch1D | tuple[Launch1D, Device]) -> int:
    return launch[0].block_size if isinstance(launch, tuple) else launch.block_size


def launch_grid_size(launch: Launch1D | tuple[Launch1D, Device]) -> int:
    return launch[0].grid_size if isinstance(launch, tuple) else launch.grid_size


def launch_shared_bytes(launch: Launch1D | Launch2D | tuple[Launch1D | Launch2D, Device]) -> int:
    return launch[0].shared_bytes if isinstance(launch, tuple) else launch.shared_bytes


def launch2d_width(launch: Launch2D | tuple[Launch2D, Device]) -> int:
    return launch[0].width if isinstance(launch, tuple) else launch.width


def launch2d_height(launch: Launch2D | tuple[Launch2D, Device]) -> int:
    return launch[0].height if isinstance(launch, tuple) else launch.height


def launch2d_threads_x(launch: Launch2D | tuple[Launch2D, Device]) -> int:
    return launch[0].block_x if isinstance(launch, tuple) else launch.block_x


def launch2d_threads_y(launch: Launch2D | tuple[Launch2D, Device]) -> int:
    return launch[0].block_y if isinstance(launch, tuple) else launch.block_y


def launch2d_grid_x(launch: Launch2D | tuple[Launch2D, Device]) -> int:
    return launch[0].grid_x if isinstance(launch, tuple) else launch.grid_x


def launch2d_grid_y(launch: Launch2D | tuple[Launch2D, Device]) -> int:
    return launch[0].grid_y if isinstance(launch, tuple) else launch.grid_y


def launch2d_device(launch: Launch2D | tuple[Launch2D, Device]) -> int:
    if isinstance(launch, tuple):
        return launch[1].ordinal
    raise ValueError("a Launch2D descriptor alone does not own a device")


def buffer_device(buffer: Buffer) -> int:
    return buffer.device.ordinal


def buffer_size(buffer: Buffer) -> int:
    return buffer.length


def buffer_elem_size(buffer: Buffer) -> int:
    return _ITEM_SIZE[buffer.dtype]


def buffer_bytes(buffer: Buffer) -> int:
    return buffer.length * _ITEM_SIZE[buffer.dtype]


def buffer_mem_kind(buffer: Buffer) -> int:
    return buffer.mem_kind


def buffer_access(buffer: Buffer) -> int:
    return buffer.access


def buffer_extent_x(buffer: Buffer) -> int:
    return buffer.extent_x


def buffer_extent_y(buffer: Buffer) -> int:
    return buffer.extent_y


def as_read_only(buffer: Buffer) -> Buffer:
    """Transfer ``buffer`` into a read-only handle aliasing the same allocation.

    Returns a new :class:`Buffer` with ``access=ACCESS_READ_ONLY`` that owns the
    device pointer. The input is marked transferred (``_transferred`` / ``_freed``)
    *without* calling ``cuMemFree``, so Aeon sees the original as consumed while
    the returned handle remains responsible for release. Prefer this over mutating
    ``access`` in place so linear ownership stays unambiguous.
    """
    buffer._ensure_ready()
    readonly = Buffer(
        buffer.device,
        buffer.pointer,
        buffer.length,
        buffer.dtype,
        mem_kind=buffer.mem_kind,
        access=ACCESS_READ_ONLY,
        extent_x=buffer.extent_x,
        extent_y=buffer.extent_y,
    )
    buffer._transferred = True
    buffer._freed = True
    return readonly


def max_allocation(device_: Device) -> int:
    return device_.max_allocation


def pending_device(pending: Pending) -> int:
    return pending.device.ordinal


def pending_size(pending: Pending) -> int:
    return pending._ensure_pending().length


def status_is_ok(status: Status) -> bool:
    status._ensure_live()
    return status.ok


def status_code(status: Status) -> int:
    status._ensure_live()
    return status.code


def check_ok(status: Status) -> None:
    status._ensure_live()
    status._consumed = True
    if not status.ok:
        raise CUDAError(status.message or f"CUDA status error {status.code}")


def discard_status(status: Status) -> None:
    status._ensure_live()
    status._consumed = True


def _coerce_values(values: Iterable[int] | Iterable[float], dtype: _DType) -> array.array[Any]:
    try:
        if dtype == "i32":
            result = array.array("i", values)
            if result.itemsize != 4:
                raise CUDAError("this Python platform does not provide a 32-bit array type")
            return result
        result = array.array("d", values)
        if result.itemsize != 8:
            raise CUDAError("this Python platform does not provide a 64-bit float array type")
        return result
    except (OverflowError, TypeError, ValueError) as exc:
        raise ValueError(f"values cannot be represented as {dtype}") from exc


def _upload(device_: Device, values: Iterable[int] | Iterable[float], dtype: _DType) -> Buffer:
    host = _coerce_values(values, dtype)
    with device_._lock:
        device_._activate()
        pointer = ctypes.c_uint64()
        allocation_size = max(1, len(host)) * _ITEM_SIZE[dtype]
        if allocation_size > device_.max_allocation:
            raise ValueError(f"allocation of {allocation_size} bytes exceeds device limit {device_.max_allocation}")
        device_._driver.check(
            device_._driver.cuMemAlloc(ctypes.byref(pointer), allocation_size),
            "cuMemAlloc",
        )
        buffer = Buffer(device_, pointer.value, len(host), dtype)
        try:
            if host:
                address, length = host.buffer_info()
                device_._driver.check(
                    device_._driver.cuMemcpyHtoD(pointer.value, ctypes.c_void_p(address), length * host.itemsize),
                    "cuMemcpyHtoD",
                )
        except BaseException:
            buffer.free()
            raise
        return buffer


def upload_i32(device_: Device, values: Iterable[int]) -> Buffer:
    return _upload(device_, values, "i32")


def upload_float64(device_: Device, values: Iterable[float]) -> Buffer:
    return _upload(device_, values, "float64")


def _download(buffer: Buffer, dtype: _DType) -> list[int] | list[float]:
    buffer._ensure_ready()
    if buffer.dtype != dtype:
        raise TypeError(f"expected a {dtype} CUDA buffer, got {buffer.dtype}")
    try:
        typecode = "i" if dtype == "i32" else "d"
        host = array.array(typecode, [0]) * buffer.length
        with buffer.device._lock:
            buffer.device._activate()
            if host:
                address, length = host.buffer_info()
                buffer.device._driver.check(
                    buffer.device._driver.cuMemcpyDtoH(
                        ctypes.c_void_p(address), buffer.pointer, length * host.itemsize
                    ),
                    "cuMemcpyDtoH",
                )
        return host.tolist()
    except BaseException:
        # The Aeon caller receives no buffer handle when download fails, so
        # release the now-unreachable allocation if possible.
        try:
            buffer.free()
        except Exception:
            pass
        raise


@dataclass(frozen=True, slots=True)
class I32Download:
    values: list[int]
    buffer: Buffer


@dataclass(frozen=True, slots=True)
class Float64Download:
    values: list[float]
    buffer: Buffer


def download_i32(buffer: Buffer) -> list[int]:
    return cast(list[int], _download(buffer, "i32"))


def download_i32_result(buffer: Buffer) -> I32Download:
    return I32Download(download_i32(buffer), buffer)


def download_float64(buffer: Buffer) -> list[float]:
    return cast(list[float], _download(buffer, "float64"))


def download_float64_result(buffer: Buffer) -> Float64Download:
    return Float64Download(download_float64(buffer), buffer)


def _vector_add(
    device_: Device, launch: Launch1D, left: Buffer, right: Buffer, dtype: _DType, stream: Stream
) -> Pending:
    if stream.device is not device_:
        raise ValueError("CUDA stream must belong to the launch device")
    if launch.block_size > device_.max_threads_per_block:
        raise ValueError(f"block size {launch.block_size} exceeds device limit {device_.max_threads_per_block}")
    if launch.shared_bytes > device_.max_shared_mem_per_block:
        raise ValueError(f"shared_bytes {launch.shared_bytes} exceeds device limit {device_.max_shared_mem_per_block}")
    if launch.require_warp_multiple:
        warp = device_.warp_size
        if launch.block_size > warp and launch.block_size % warp != 0:
            raise ValueError(f"block size {launch.block_size} must be a multiple of warp size {warp}")
    for operand in (left, right):
        operand._ensure_ready()
        if operand.device is not device_:
            raise ValueError("all CUDA buffers must belong to the launch device")
        if operand.dtype != dtype:
            raise TypeError(f"expected {dtype} CUDA buffers")
        if operand.mem_kind != MEM_KIND_DEVICE:
            raise ValueError("kernel operands must be device buffers")
    if left.length != right.length or launch.size != left.length:
        raise ValueError("launch size and both buffer lengths must match")

    with device_._lock:
        device_._activate()
        pointer = ctypes.c_uint64()
        device_._driver.check(
            device_._driver.cuMemAlloc(ctypes.byref(pointer), max(1, launch.size) * _ITEM_SIZE[dtype]),
            "cuMemAlloc",
        )
        output = Buffer(
            device_,
            pointer.value,
            launch.size,
            dtype,
            mem_kind=MEM_KIND_DEVICE,
            access=ACCESS_READ_WRITE,
        )
        try:
            if launch.size:
                function = device_._function(dtype)
                left_arg = ctypes.c_uint64(left.pointer)
                right_arg = ctypes.c_uint64(right.pointer)
                output_arg = ctypes.c_uint64(output.pointer)
                size_arg = ctypes.c_int32(launch.size)
                arguments = (ctypes.c_void_p * 4)(
                    ctypes.addressof(left_arg),
                    ctypes.addressof(right_arg),
                    ctypes.addressof(output_arg),
                    ctypes.addressof(size_arg),
                )
                device_._driver.check(
                    device_._driver.cuLaunchKernel(
                        function,
                        launch.grid_size,
                        1,
                        1,
                        launch.block_size,
                        1,
                        1,
                        launch.shared_bytes,
                        ctypes.c_void_p(stream.stream_id),
                        arguments,
                        None,
                    ),
                    "cuLaunchKernel",
                )
        except BaseException:
            output.free()
            raise
        return Pending(output, (left, right), stream)


def vector_add_i32(device_: Device, launch: Launch1D, left: Buffer, right: Buffer, stream: Stream) -> Pending:
    return _vector_add(device_, launch, left, right, "i32", stream)


def vector_add_float64(device_: Device, launch: Launch1D, left: Buffer, right: Buffer, stream: Stream) -> Pending:
    return _vector_add(device_, launch, left, right, "float64", stream)


def synchronize(pending: Pending) -> Buffer:
    return pending.synchronize()


def synchronize_with_status(pending: Pending) -> StatusBuffer:
    """Like :func:`synchronize`, but returns a :class:`StatusBuffer` instead of raising.

    On success the status is ok and ``buffer`` holds the ready output. On failure
    resources are released when possible and ``buffer`` is ``None``.
    """
    try:
        buffer = pending.synchronize()
        return StatusBuffer(Status(ok=True), buffer)
    except CUDAError as exc:
        try:
            pending.discard()
        except Exception:
            pass
        return StatusBuffer(Status(ok=False, code=1, message=str(exc)), None)


def status_buffer_ok(result: StatusBuffer) -> bool:
    return result.status.ok


def unpack_status_buffer(result: StatusBuffer) -> tuple[Status, Buffer | None]:
    return (result.status, result.buffer)


def status_pair_status(pair: tuple[Status, Buffer | None]) -> Status:
    return pair[0]


def status_pair_buffer(pair: tuple[Status, Buffer | None]) -> Buffer:
    buffer = pair[1]
    if buffer is None:
        raise CUDAStateError("CUDA status buffer has no ready allocation")
    return buffer


def free(buffer: Buffer) -> None:
    buffer.free()


def discard(pending: Pending) -> None:
    pending.discard()


def close(device_: Device) -> None:
    device_.close()


def _compile_vector_add_ptx(compute_capability: tuple[int, int]) -> str:
    """Generate the two fixed vector-add kernels and compile them to PTX."""
    try:
        import llvmlite.binding as llvm
        import llvmlite.ir as ir
    except ImportError as exc:
        raise CUDAUnavailableError("llvmlite is required to generate CUDA kernels") from exc

    module = ir.Module(name="aeon_cuda_vector_add")
    module.triple = "nvptx64-nvidia-cuda"
    module.data_layout = "e-i64:64-i128:128-v16:16-v32:32-n16:32:64-S128-p1:64:64-p2:32:32-p3:32:32-p4:64:64-p5:32:32"
    i32 = ir.IntType(32)
    tid = ir.Function(module, ir.FunctionType(i32, []), name="llvm.nvvm.read.ptx.sreg.tid.x")
    ctaid = ir.Function(module, ir.FunctionType(i32, []), name="llvm.nvvm.read.ptx.sreg.ctaid.x")
    ntid = ir.Function(module, ir.FunctionType(i32, []), name="llvm.nvvm.read.ptx.sreg.ntid.x")

    kernels: list[Any] = []
    for dtype_value, element in (("i32", i32), ("float64", ir.DoubleType())):
        dtype = cast(_DType, dtype_value)
        pointer = ir.PointerType(element, addrspace=1)
        kernel = ir.Function(
            module,
            ir.FunctionType(ir.VoidType(), [pointer, pointer, pointer, i32]),
            name=_KERNEL_NAME[dtype].decode("ascii"),
        )
        left, right, output, size = kernel.args
        block = kernel.append_basic_block("entry")
        body = kernel.append_basic_block("body")
        done = kernel.append_basic_block("done")
        builder = ir.IRBuilder(block)
        index = builder.add(builder.mul(builder.call(ctaid, []), builder.call(ntid, [])), builder.call(tid, []))
        builder.cbranch(builder.icmp_signed("<", index, size), body, done)
        builder.position_at_end(body)
        left_value = builder.load(builder.gep(left, [index]))
        right_value = builder.load(builder.gep(right, [index]))
        value = builder.add(left_value, right_value) if dtype == "i32" else builder.fadd(left_value, right_value)
        builder.store(value, builder.gep(output, [index]))
        builder.branch(done)
        builder.position_at_end(done)
        builder.ret_void()
        kernels.append(kernel)

    annotations = module.add_named_metadata("nvvm.annotations")
    for kernel in kernels:
        annotations.add(module.add_metadata([kernel, "kernel", ir.Constant(i32, 1)]))

    try:
        llvm.initialize_all_targets()
        llvm.initialize_all_asmprinters()
        parsed = llvm.parse_assembly(str(module))
        parsed.verify()
        target = llvm.Target.from_triple(module.triple)
        major, minor = compute_capability
        machine = target.create_target_machine(cpu=f"sm_{major}{minor}", opt=2)
        return str(machine.emit_assembly(parsed))
    except Exception as exc:
        raise CUDAError(
            f"NVPTX compilation failed for sm_{compute_capability[0]}{compute_capability[1]}: {exc}"
        ) from exc


# Names used by native expressions in Cuda.ae.  Keeping these aliases here also
# makes the Python binding convenient to exercise without the Aeon evaluator.
Cuda_device = device
Cuda_num_devices = num_devices
Cuda_launch_1d = launch_1d
Cuda_launch_1d_warped = launch_1d_warped
Cuda_launch_2d = launch_2d
Cuda_launch_grid_size = launch_grid_size
Cuda_launch_shared_bytes = launch_shared_bytes
Cuda_upload_i32 = upload_i32
Cuda_upload_float64 = upload_float64
Cuda_download_i32 = download_i32
Cuda_download_i32_result = download_i32_result
Cuda_download_float64 = download_float64
Cuda_download_float64_result = download_float64_result
Cuda_vector_add_i32 = vector_add_i32
Cuda_vector_add_float64 = vector_add_float64
Cuda_synchronize = synchronize
Cuda_synchronize_with_status = synchronize_with_status
Cuda_as_read_only = as_read_only
Cuda_free = free
Cuda_discard = discard
Cuda_close = close
Cuda_buffer_mem_kind = buffer_mem_kind
Cuda_buffer_access = buffer_access
Cuda_buffer_extent_x = buffer_extent_x
Cuda_buffer_extent_y = buffer_extent_y
Cuda_max_shared_mem_per_block = max_shared_mem_per_block
Cuda_warp_size = warp_size
Cuda_status_is_ok = status_is_ok
Cuda_status_code = status_code
Cuda_check_ok = check_ok
Cuda_discard_status = discard_status
Cuda_status_buffer_ok = status_buffer_ok
Cuda_unpack_status_buffer = unpack_status_buffer
Cuda_status_pair_status = status_pair_status
Cuda_status_pair_buffer = status_pair_buffer
Cuda_MEM_KIND_DEVICE = MEM_KIND_DEVICE
Cuda_MEM_KIND_HOST_PINNED = MEM_KIND_HOST_PINNED
Cuda_MEM_KIND_MANAGED = MEM_KIND_MANAGED
Cuda_MEM_KIND_HOST = MEM_KIND_HOST
Cuda_ACCESS_READ_ONLY = ACCESS_READ_ONLY
Cuda_ACCESS_READ_WRITE = ACCESS_READ_WRITE

__all__ = [
    "ACCESS_READ_ONLY",
    "ACCESS_READ_WRITE",
    "Buffer",
    "CUDAError",
    "CUDAStateError",
    "CUDAUnavailableError",
    "Device",
    "Float64Download",
    "I32Download",
    "Launch1D",
    "Launch2D",
    "MEM_KIND_DEVICE",
    "MEM_KIND_HOST",
    "MEM_KIND_HOST_PINNED",
    "MEM_KIND_MANAGED",
    "Pending",
    "Status",
    "StatusBuffer",
    "Stream",
    "as_read_only",
    "buffer_access",
    "buffer_bytes",
    "buffer_device",
    "buffer_elem_size",
    "buffer_extent_x",
    "buffer_extent_y",
    "buffer_mem_kind",
    "buffer_size",
    "check_ok",
    "close",
    "create_stream",
    "default_stream",
    "device",
    "device_id",
    "discard",
    "discard_status",
    "download_float64",
    "download_float64_result",
    "download_i32",
    "download_i32_result",
    "free",
    "launch2d_device",
    "launch2d_grid_x",
    "launch2d_grid_y",
    "launch2d_height",
    "launch2d_threads_x",
    "launch2d_threads_y",
    "launch2d_width",
    "launch_1d",
    "launch_1d_warped",
    "launch_2d",
    "launch_device",
    "launch_grid_size",
    "launch_items",
    "launch_shared_bytes",
    "launch_threads",
    "max_allocation",
    "max_shared_mem_per_block",
    "max_threads_per_block",
    "num_devices",
    "pending_device",
    "pending_size",
    "pending_stream",
    "status_buffer_ok",
    "status_code",
    "status_is_ok",
    "status_pair_buffer",
    "status_pair_status",
    "stream_device",
    "stream_id",
    "synchronize",
    "synchronize_with_status",
    "unpack_status_buffer",
    "upload_float64",
    "upload_i32",
    "vector_add_float64",
    "vector_add_i32",
    "warp_size",
]
