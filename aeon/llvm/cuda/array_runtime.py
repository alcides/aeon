"""Stream-ordered array launches, bounded reusable buffers, and deferred completion."""

from __future__ import annotations

import ctypes
import weakref
from collections import defaultdict
from types import SimpleNamespace

from aeon.bindings.ndarray import NDArray, ManagedArray, ReadOnlyBuffer
from aeon.llvm.llvm_ast import LLVMNDArrayType, LLVMPointerType
from aeon.llvm.ndarray import pack_descriptor, descriptor_shape
from aeon.llvm.utils import sanitize_name


class ArrayRuntime:
    CACHE_LIMIT = 64 * 1024 * 1024
    BATCH_LIMIT = 256

    def __init__(self, engine):
        self.engine = engine
        self.free: dict[int, list] = defaultdict(list)
        self.cached = 0
        self.pinned = []
        self.checks = []
        self.outputs = weakref.WeakSet()
        self.launches = 0
        self.pending = False
        lib = engine.libcuda
        lib.cuMemHostAlloc.argtypes = [ctypes.POINTER(ctypes.c_void_p), ctypes.c_size_t, ctypes.c_uint]
        lib.cuMemFreeHost.argtypes = [ctypes.c_void_p]
        lib.cuMemcpyHtoDAsync_v2.argtypes = [ctypes.c_uint64, ctypes.c_void_p, ctypes.c_size_t, ctypes.c_void_p]
        lib.cuMemsetD8Async.argtypes = [ctypes.c_uint64, ctypes.c_ubyte, ctypes.c_size_t, ctypes.c_void_p]

    def check(self, code, operation):
        if code:
            from aeon.llvm.cuda.executor import CUDAExecutionError

            raise CUDAExecutionError(f"{operation}: {self.engine._cuda_error_name(code)}")

    def allocate(self, size):
        size = max(4, 1 << (max(1, size) - 1).bit_length())
        if self.free[size]:
            self.cached -= size
            return self.free[size].pop(), size
        pointer = ctypes.c_uint64()
        self.check(self.engine.libcuda.cuMemAlloc_v2(ctypes.byref(pointer), size), "cuMemAlloc for array pipeline")
        return pointer, size

    def release(self, allocation):
        pointer, size = allocation
        # All uses and subsequent overwrites are ordered on this context's default stream.
        self.free[size].append(pointer)
        self.cached += size

    def upload_descriptor(self, descriptor):
        allocation = self.allocate(ctypes.sizeof(descriptor))
        try:
            host = ctypes.c_void_p()
            self.check(
                self.engine.libcuda.cuMemHostAlloc(ctypes.byref(host), ctypes.sizeof(descriptor), 0), "cuMemHostAlloc"
            )
            self.pinned.append(host)
            ctypes.memmove(host, ctypes.byref(descriptor), ctypes.sizeof(descriptor))
            self.check(
                self.engine.libcuda.cuMemcpyHtoDAsync_v2(allocation[0].value, host, ctypes.sizeof(descriptor), None),
                "cuMemcpyHtoDAsync descriptor",
            )
            self.pending = True
            return allocation
        except Exception:
            self.release(allocation)
            raise

    def resident(self, array, ty, overwrite=False):
        from aeon.llvm.cuda.executor import DeviceArray

        storage = array._storage
        if storage.failure is not None:
            storage.read()
        ctype = self.engine._get_ctypes_type(ty.element_type)
        existing = storage.device
        zero = storage.zero_version == storage.version and storage.host_current and not storage.exposed
        if (
            existing is not None
            and existing.engine is self.engine
            and existing.ctype == ctype
            and existing.count == len(storage.host)
        ):
            if overwrite:
                existing.version = storage.version
                return existing
            if zero and existing.version != storage.version:
                self.check(
                    self.engine.libcuda.cuMemsetD8Async(
                        existing.pointer.value, 0, existing.count * ctypes.sizeof(ctype), None
                    ),
                    "cuMemsetD8Async",
                )
                self.pending = True
                existing.version = storage.version
                return existing
            return self.engine._device_array(storage, ctype)
        if not overwrite and not zero:
            return self.engine._device_array(storage, ctype)
        if existing is not None:
            existing.close()
        resident = DeviceArray.__new__(DeviceArray)
        resident.engine, resident.storage, resident.ctype = self.engine, weakref.ref(storage), ctype
        resident.count, resident.version, resident.host_snapshot = len(storage.host), storage.version, ()
        resident.pointer, resident.pool_size = self.allocate(resident.count * ctypes.sizeof(ctype))
        storage.device = resident
        self.engine._resident_arrays.add(resident)
        if zero and not overwrite:
            self.check(
                self.engine.libcuda.cuMemsetD8Async(
                    resident.pointer.value, 0, resident.count * ctypes.sizeof(ctype), None
                ),
                "cuMemsetD8Async",
            )
            self.pending = True
        return resident

    def launch(self, module, name, parameters, count, axis=False):
        function = self.engine._get_function(module, name)
        addresses = (ctypes.c_void_p * len(parameters))(*[ctypes.addressof(value) for value in parameters])
        grid, block = self.engine._launch_dimensions((count,))
        if axis:
            grid = (max(1, count), 1, 1)
        if count:
            self.check(
                self.engine.libcuda.cuLaunchKernel(function, *grid, *block, 0, None, addresses, None),
                "cuLaunchKernel array pipeline",
            )
            self.launches += 1
            self.pending = True

    def synchronize(self, completed=False):
        self.engine._activate()
        try:
            if self.pending and not completed:
                self.check(self.engine.libcuda.cuCtxSynchronize(), "Deferred CUDA execution")
            for allocation, descriptor, array, address in self.checks:
                self.check(
                    self.engine.libcuda.cuMemcpyDtoH_v2(
                        ctypes.byref(descriptor), allocation[0].value, ctypes.sizeof(descriptor)
                    ),
                    "cuMemcpyDtoH descriptor",
                )
                descriptor_shape(descriptor, array, address)
        except Exception as error:
            for storage in self.outputs:
                storage.failure = error
            raise
        finally:
            self.pending = False
            self.launches = 0
            self.outputs.clear()
            for allocation, _, _, _ in self.checks:
                self.release(allocation)
            self.checks.clear()
            for pointer in self.pinned:
                self.engine.libcuda.cuMemFreeHost(pointer)
            self.pinned.clear()
            self.trim()

    def trim(self, limit=None):
        limit = self.CACHE_LIMIT if limit is None else limit
        if self.pending:
            return
        for size in sorted(self.free, reverse=True):
            while self.free[size] and self.cached > limit:
                pointer = self.free[size].pop()
                self.check(self.engine.libcuda.cuMemFree_v2(pointer.value), "cuMemFree array pool")
                self.cached -= size

    def boundary(self):
        if self.launches >= self.BATCH_LIMIT or self.cached > self.CACHE_LIMIT:
            self.synchronize()
        # Empty-array calls still enqueue descriptor copies and retain staging memory.
        self.launches += 1


def runtime(engine):
    if not hasattr(engine, "_array_runtime"):
        engine._array_runtime = ArrayRuntime(engine)
    return engine._array_runtime


def module_for(engine, code):
    key = hash(code)
    if key not in engine._module_cache:
        engine._module_cache[key] = engine._load_module(engine._compile_to_ptx(code))
    return engine._module_cache[key]


def marshal(state, arguments, types, destination, overwrite, checked=False):
    values, allocations = [], []
    try:
        for argument, ty in zip(arguments, types):
            if isinstance(ty, (LLVMNDArrayType, LLVMPointerType)) and isinstance(
                argument, (NDArray, ManagedArray, ReadOnlyBuffer)
            ):
                if isinstance(ty, LLVMNDArrayType) and argument.rank != ty.rank:
                    raise ValueError("Array pipeline argument rank does not match")
                resident = state.resident(argument, ty, overwrite=argument is destination and overwrite)
                if isinstance(ty, LLVMNDArrayType):
                    descriptor = pack_descriptor(argument, resident.pointer.value)
                    allocation = state.upload_descriptor(descriptor)
                    values.append(allocation[0])
                    if checked:
                        state.checks.append(
                            (
                                allocation,
                                descriptor,
                                SimpleNamespace(elements=argument.elements),
                                resident.pointer.value,
                            )
                        )
                    else:
                        allocations.append(allocation)
                else:
                    values.append(resident.pointer)
            else:
                values.append(state.engine._get_ctypes_type(ty)(argument))
        return values, allocations
    except Exception:
        for allocation in allocations:
            state.release(allocation)
        state.synchronize()
        raise


def execute_array(engine, code, function, arguments, operation):
    engine._activate()
    state = runtime(engine)
    state.boundary()
    module = module_for(engine, code)
    destination = arguments[-1]
    values_by_name = dict(zip(function.arg_names, arguments))
    source = values_by_name[operation.array.name]
    # Only a distinct, newly allocated destination can skip its initial upload.
    params, allocations = marshal(state, arguments, function.arg_types, destination, destination is not source)
    name = sanitize_name(function.name)
    storage = destination._storage
    state.outputs.add(storage)
    try:
        if operation.op.startswith("scan"):
            element = engine._get_ctypes_type(operation.type.element_type)
            source_pointer = source._storage.device.pointer
            count = source.elements
            levels = []
            while count:
                blocks = (count + 255) // 256
                prefix = state.allocate(count * ctypes.sizeof(element))
                totals = state.allocate(blocks * ctypes.sizeof(element))
                allocations.extend([prefix, totals])
                state.launch(
                    module,
                    name + "__kernel",
                    [*params, source_pointer, ctypes.c_int32(count), prefix[0], totals[0]],
                    count,
                )
                levels.append((prefix[0], count))
                if blocks == 1:
                    break
                source_pointer, count = totals[0], blocks
            for index in range(len(levels) - 2, -1, -1):
                prefix, count = levels[index]
                state.launch(
                    module, name + "__offsets", [*params, prefix, levels[index + 1][0], ctypes.c_int32(count)], count
                )
            if levels:
                state.launch(module, name + "__seed", [*params, levels[0][0]], destination.elements)
        else:
            state.launch(module, name + "__kernel", params, destination.elements, axis=operation.op == "reduce_axis")
        storage.host_current = False
        storage.device.version = storage.version
        if storage.exposed:
            storage.read()
        return destination
    except Exception as error:
        storage.failure = error
        state.synchronize()
        raise
    finally:
        for allocation in allocations:
            state.release(allocation)


def execute_resident(engine, code, name, arguments, types, output_index, shape):
    """Existing fill/map_rows wrappers also defer descriptor/error observation."""
    engine._activate()
    state = runtime(engine)
    state.boundary()
    module = module_for(engine, code)
    destination = arguments[output_index]
    params, allocations = marshal(state, arguments, types, destination, False, checked=True)
    result = state.allocate(8)
    allocations.append(result)
    params.append(result[0])
    storage = destination._storage
    state.outputs.add(storage)
    try:
        function = engine._get_function(module, name + "__kernel")
        addresses = (ctypes.c_void_p * len(params))(*[ctypes.addressof(value) for value in params])
        grid, block = engine._launch_dimensions(shape)
        state.check(
            engine.libcuda.cuLaunchKernel(function, *grid, *block, 0, None, addresses, None),
            "cuLaunchKernel array pipeline",
        )
        state.pending = True
        state.launches += 1
        storage.host_current = False
        if storage.exposed:
            storage.read()
        return destination
    except Exception as error:
        storage.failure = error
        state.synchronize()
        raise
    finally:
        for allocation in allocations:
            state.release(allocation)
