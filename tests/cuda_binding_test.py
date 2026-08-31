from __future__ import annotations

import gc
import importlib
import sys

import pytest


@pytest.fixture
def cuda_module():
    sys.modules.pop("aeon.bindings.cuda", None)
    module = importlib.import_module("aeon.bindings.cuda")
    yield module
    driver = module._DRIVER
    module._DRIVER = None
    del driver
    gc.collect()


def test_import_does_not_initialize_cuda(cuda_module):
    assert cuda_module._DRIVER is None


def test_num_devices_reports_available_hardware(cuda_module):
    try:
        count = cuda_module.num_devices()
    except cuda_module.CUDAError as exc:
        pytest.skip(f"CUDA hardware is unavailable: {exc}")
    assert count > 0
    with pytest.raises(cuda_module.CUDAUnavailableError):
        cuda_module.device(count)


def test_launch_1d_validates_and_rounds_up(cuda_module):
    assert cuda_module.Launch1D(1, 1).grid_size == 1
    assert cuda_module.Launch1D(33, 32).grid_size == 2

    for size, block_size in ((0, 1), (-1, 1), (1, 0), (32, 33), (2048, 1025), (True, 1)):
        with pytest.raises(ValueError):
            cuda_module.Launch1D(size, block_size)


def test_ptx_contains_fixed_vector_add_kernels(cuda_module):
    ptx = cuda_module._compile_vector_add_ptx((8, 6))
    assert ".visible .entry aeon_vector_add_i32" in ptx
    assert ".visible .entry aeon_vector_add_float64" in ptx


def _cuda_device_or_skip(cuda_module):
    try:
        return cuda_module.Device()
    except cuda_module.CUDAError as exc:
        pytest.skip(f"CUDA hardware is unavailable: {exc}")


def test_i32_upload_add_download_and_lifecycle(cuda_module):
    device = _cuda_device_or_skip(cuda_module)
    try:
        left = cuda_module.upload_i32(device, [1, -2, 3, 2**31 - 1])
        right = cuda_module.upload_i32(device, [4, 8, -3, -1])
        pending = cuda_module.vector_add_i32(device, cuda_module.Launch1D(4, 4), left, right)
        output = pending.synchronize()

        expected = [5, 6, 0, 2**31 - 2]
        first = cuda_module.download_i32(output)
        second = cuda_module.download_i32(output)
        assert first == expected
        assert second == expected
        assert first is not second
        assert not output._freed
        with pytest.raises(cuda_module.CUDAStateError):
            pending.synchronize()

        left.free()
        left.free()
        with pytest.raises(cuda_module.CUDAStateError):
            cuda_module.download_i32(left)
        assert right._freed

        output.free()
        with pytest.raises(cuda_module.CUDAStateError):
            cuda_module.download_i32(output)
        output.free()
    finally:
        device.close()
        device.close()


def test_download_failure_releases_buffer(cuda_module):
    device = _cuda_device_or_skip(cuda_module)
    try:
        buffer = cuda_module.upload_i32(device, [1])

        def fail_copy(*args):
            raise cuda_module.CUDAError("copy failed")

        device._driver.cuMemcpyDtoH = fail_copy
        with pytest.raises(cuda_module.CUDAError, match="copy failed"):
            cuda_module.download_i32(buffer)
        assert buffer._freed
    finally:
        device.close()


def test_float64_upload_add_download_and_discard(cuda_module):
    device = _cuda_device_or_skip(cuda_module)
    try:
        left = cuda_module.upload_float64(device, [0.5, -2.25, 1e100])
        right = cuda_module.upload_float64(device, [1.25, 0.25, -1e100])
        pending = cuda_module.vector_add_float64(device, cuda_module.launch_1d(3), left, right)
        output = pending._output
        pending.discard()
        pending.discard()

        assert output is not None
        with pytest.raises(cuda_module.CUDAStateError):
            cuda_module.download_float64(output)
        with pytest.raises(cuda_module.CUDAStateError):
            pending.synchronize()
        assert left._freed
        assert right._freed
    finally:
        device.close()


def test_rejects_mismatched_buffers_without_allocating_output(cuda_module):
    device = _cuda_device_or_skip(cuda_module)
    try:
        ints = cuda_module.upload_i32(device, [1, 2])
        floats = cuda_module.upload_float64(device, [1.0, 2.0])
        with pytest.raises(TypeError):
            cuda_module.vector_add_i32(device, cuda_module.launch_1d(2), ints, floats)
        with pytest.raises(ValueError):
            cuda_module.vector_add_i32(device, cuda_module.launch_1d(1), ints, ints)
        ints.free()
        floats.free()
    finally:
        device.close()


def test_device_close_cleans_live_buffers_and_pending_results(cuda_module):
    device = _cuda_device_or_skip(cuda_module)
    left = cuda_module.upload_i32(device, [1])
    right = cuda_module.upload_i32(device, [2])
    pending = cuda_module.vector_add_i32(device, cuda_module.launch_1d(1), left, right)
    output = pending._output

    device.close()

    assert left._freed
    assert right._freed
    assert output is not None and output._freed
    with pytest.raises(cuda_module.CUDAStateError):
        pending.synchronize()


def test_unavailable_driver_is_reported_only_on_first_operation(cuda_module, monkeypatch):
    def unavailable():
        raise OSError("no CUDA")

    monkeypatch.setattr(cuda_module.ctypes.util, "find_library", lambda name: None)
    monkeypatch.setattr(cuda_module.ctypes, "CDLL", lambda name: unavailable())

    assert cuda_module._DRIVER is None
    with pytest.raises(cuda_module.CUDAUnavailableError, match="not found"):
        cuda_module.Device()
