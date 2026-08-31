"""Compile-time protocol tests for the explicit ``Cuda`` module.

These tests do not initialize CUDA or require a GPU.  They exercise module
scoping, the QTT ownership discipline of ``Buffer``/``Pending``, and the
refinements connecting devices, launch configurations, and vector sizes.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from aeon.facade.api import (
    LinearityError,
    LinearTypeNotBoundLinearlyError,
    LinearUnusedError,
    LinearUsedTooManyTimesError,
)
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SilentSynthesisUI

MAIN = '\ndef main (args: Int) : Unit := print "ok";\n'
IMPORTS = """
open Array
open Cuda
"""


def _errors(source: str):
    """Compile ``source`` without evaluating native CUDA operations."""
    setup_logger()
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    return list(AeonDriver(cfg).parse(aeon_code=source))


def _linearity_errors(source: str):
    return [error for error in _errors(source) if isinstance(error, LinearityError)]


def _int_array(values: tuple[int, ...]) -> str:
    expression = "Array.new{Int} unit"
    for value in values:
        expression = f"Array.append ({expression}) {value}"
    return expression


def _float_array(values: tuple[float, ...]) -> str:
    expression = "Array.new{Float} unit"
    for value in values:
        expression = f"Array.append ({expression}) ({value} : Float)"
    return expression


# ---------------------------------------------------------------------------
# Module scoping
# ---------------------------------------------------------------------------


def test_cuda_names_are_not_in_the_global_prelude():
    device_errors = [str(error) for error in _errors("def probe (u: Unit) : Int := device_id u;" + MAIN)]
    default_errors = [str(error) for error in _errors("def probe (u: Unit) : Int := default_device u;" + MAIN)]
    assert any("device_id" in error and "does not exist" in error for error in device_errors), device_errors
    assert any("default_device" in error and "does not exist" in error for error in default_errors), default_errors


def test_import_cuda_keeps_api_qualified():
    source = (
        """
import Cuda;

def selected (u: Unit) : Int := Cuda.device_id (Cuda.default_device u);
def count (u: Unit) : Int := Cuda.num_devices u;
"""
        + MAIN
    )
    assert _errors(source) == []


def test_num_devices_is_positive():
    source = IMPORTS + "def count (u: Unit) : {n: Int | n > 0} := num_devices u;" + MAIN
    assert _errors(source) == []


def test_upload_respects_allocation_byte_bound():
    source = (
        IMPORTS
        + f"""
def bounded (d: Device) : Unit :=
    let 1 xs := {_int_array((1, 2))} in
    let 1 buffer := upload_i32 d xs in
    free buffer;
"""
        + MAIN
    )
    assert _errors(source) == []


def test_open_cuda_exposes_descriptors_and_launch_measures():
    source = (
        IMPORTS
        + """
def descriptors (d: Device) (l: Launch1D) : Int :=
    device_id d + max_threads_per_block d + num_devices unit
    + launch_items l + launch_device l + launch_threads l + launch_grid_size l;
"""
        + MAIN
    )
    assert _errors(source) == []


# ---------------------------------------------------------------------------
# Legal protocols
# ---------------------------------------------------------------------------


def test_launch_grid_covers_items_at_compile_time():
    source = (
        IMPORTS
        + """
def covered (u: Unit) : Int :=
    let d := default_device u in
    let stream := default_stream d in
    let launch := launch_1d d 33 1 in
    launch_grid_size launch * launch_threads launch;
"""
        + MAIN
    )
    assert _errors(source) == []


def test_i32_upload_add_synchronize_download_lifecycle_typechecks():
    source = (
        IMPORTS
        + f"""
def lifecycle (u: Unit) : Int :=
    let d := default_device u in
    let stream := default_stream d in
    let launch := launch_1d d 3 1 in
    let 1 xs := {_int_array((1, 2, 3))} in
    let 1 ys := {_int_array((10, 20, 30))} in
    let 1 left := upload_i32 d xs in
    let 1 right := upload_i32 d ys in
    let 1 pending := add_i32 launch stream left right in
    let 1 ready := synchronize pending in
    let 1 downloaded := download_i32 ready in
    let pair := unpack_i32_download downloaded in
    let 1 values := download_values_i32 pair in
    let 1 next := download_buffer_i32 pair in
    let total := Array.sum values in
    let _ := free next in
    total;
"""
        + MAIN
    )
    assert _errors(source) == []


def test_float64_lifecycle_and_explicit_terminal_operations_typecheck():
    source = (
        IMPORTS
        + f"""
def lifecycle (u: Unit) : Unit :=
    let d := default_device u in
    let stream := default_stream d in
    let launch := launch_1d d 2 1 in
    let 1 xs := {_float_array((1.5, 2.5))} in
    let 1 ys := {_float_array((3.5, 4.5))} in
    let 1 left := upload_float64 d xs in
    let 1 right := upload_float64 d ys in
    let 1 pending := add_float64 launch stream left right in
    let 1 ready := synchronize pending in
    let 1 downloaded := download_float64 ready in
    let pair := unpack_float64_download downloaded in
    let 1 values := download_values_float64 pair in
    let 1 next := download_buffer_float64 pair in
    let _ := Array.length values in
    let _ := free next in
    let 1 spare := upload_i32 d ({_int_array((7,))}) in
    free spare;

def abandon (u: Unit) : Unit :=
    let d := default_device u in
    let stream := default_stream d in
    let launch := launch_1d d 1 1 in
    let 1 left := upload_i32 d ({_int_array((1,))}) in
    let 1 right := upload_i32 d ({_int_array((2,))}) in
    let 1 pending := add_i32 launch stream left right in
    discard pending;
"""
        + MAIN
    )
    assert _errors(source) == []


# ---------------------------------------------------------------------------
# QTT ownership failures
# ---------------------------------------------------------------------------


def test_leaked_buffer_is_rejected():
    source = (
        IMPORTS
        + f"""
def leak (d: Device) : Int :=
    let 1 buffer := upload_i32 d ({_int_array((1,))}) in
    0;
"""
        + MAIN
    )
    assert any(isinstance(error, LinearUnusedError) for error in _linearity_errors(source))


def test_leaked_pending_is_rejected():
    source = (
        IMPORTS
        + f"""
def leak (d: Device) : Int :=
    let stream := default_stream d in
    let launch := launch_1d d 1 1 in
    let 1 left := upload_i32 d ({_int_array((1,))}) in
    let 1 right := upload_i32 d ({_int_array((2,))}) in
    let 1 pending := add_i32 launch stream left right in
    0;
"""
        + MAIN
    )
    assert any(isinstance(error, LinearUnusedError) for error in _linearity_errors(source))


def test_linear_result_requires_a_multiplicity_one_binder():
    source = (
        IMPORTS
        + f"""
def bad_binder (d: Device) : Unit :=
    let buffer := upload_i32 d ({_int_array((1,))}) in
    free buffer;
"""
        + MAIN
    )
    assert any(isinstance(error, LinearTypeNotBoundLinearlyError) for error in _linearity_errors(source))


def test_double_free_is_rejected():
    source = (
        IMPORTS
        + f"""
def double_free (d: Device) : Unit :=
    let 1 buffer := upload_i32 d ({_int_array((1,))}) in
    let _ := free buffer in
    free buffer;
"""
        + MAIN
    )
    assert any(isinstance(error, LinearUsedTooManyTimesError) for error in _linearity_errors(source))


def test_stale_input_handle_after_launch_is_rejected():
    source = (
        IMPORTS
        + f"""
def stale (d: Device) : Unit :=
    let stream := default_stream d in
    let launch := launch_1d d 1 1 in
    let 1 left := upload_i32 d ({_int_array((1,))}) in
    let 1 right := upload_i32 d ({_int_array((2,))}) in
    let 1 pending := add_i32 launch stream left right in
    let _ := discard pending in
    free left;
"""
        + MAIN
    )
    assert any(isinstance(error, LinearUsedTooManyTimesError) for error in _linearity_errors(source))


def test_download_can_be_repeated_without_nesting():
    source = (
        IMPORTS
        + f"""
def repeated (d: Device) : Int :=
    let stream := default_stream d in
    let 1 ready0 := upload_i32 d ({_int_array((1, 2, 3))}) in
    let 1 downloaded0 := download_i32 ready0 in
    let pair0 := unpack_i32_download downloaded0 in
    let 1 values0 := download_values_i32 pair0 in
    let 1 ready1 := download_buffer_i32 pair0 in
    let 1 downloaded1 := download_i32 ready1 in
    let pair1 := unpack_i32_download downloaded1 in
    let 1 values1 := download_values_i32 pair1 in
    let 1 ready2 := download_buffer_i32 pair1 in
    let first := Array.sum values0 in
    let second := Array.sum values1 in
    let _ := free ready2 in
    first + second;
"""
        + MAIN
    )
    assert _errors(source) == []


def test_download_preserves_size_and_device_refinements():
    source = (
        IMPORTS
        + f"""
def preserved (u: Unit) : Int :=
    let d := default_device u in
    let stream := default_stream d in
    let launch := launch_1d d 3 1 in
    let 1 ready0 := upload_i32 d ({_int_array((1, 2, 3))}) in
    let 1 downloaded0 := download_i32 ready0 in
    let pair0 := unpack_i32_download downloaded0 in
    let 1 values0 := download_values_i32 pair0 in
    let 1 ready1 := download_buffer_i32 pair0 in
    let total0 := Array.sum values0 in
    let 1 other := upload_i32 d ({_int_array((4, 5, 6))}) in
    let 1 pending := add_i32 launch stream ready1 other in
    let 1 ready2 := synchronize pending in
    let 1 downloaded1 := download_i32 ready2 in
    let pair1 := unpack_i32_download downloaded1 in
    let 1 values1 := download_values_i32 pair1 in
    let 1 ready3 := download_buffer_i32 pair1 in
    let result := Array.sum values1 in
    let _ := free ready3 in
    result;
"""
        + MAIN
    )
    assert _errors(source) == []


def test_download_result_must_free_recovered_buffer():
    source = (
        IMPORTS
        + f"""
def leak_successor (d: Device) : Int :=
    let stream := default_stream d in
    let 1 ready := upload_i32 d ({_int_array((1,))}) in
    let 1 downloaded := download_i32 ready in
    let pair := unpack_i32_download downloaded in
    let 1 values := download_values_i32 pair in
    let 1 next := download_buffer_i32 pair in
    Array.sum values;
"""
        + MAIN
    )
    assert any(isinstance(error, LinearUnusedError) for error in _linearity_errors(source))


def test_download_consumes_outer_buffer_handle():
    source = (
        IMPORTS
        + f"""
def stale (d: Device) : Unit :=
    let stream := default_stream d in
    let 1 ready := upload_i32 d ({_int_array((1,))}) in
    let 1 downloaded := download_i32 ready in
    let pair := unpack_i32_download downloaded in
    let 1 values := download_values_i32 pair in
    let 1 next := download_buffer_i32 pair in
    let _ := Array.sum values in
    let _ := free next in
    free ready;
"""
        + MAIN
    )
    assert any(isinstance(error, LinearUsedTooManyTimesError) for error in _linearity_errors(source))


def test_pending_cannot_be_downloaded_before_synchronize():
    source = (
        IMPORTS
        + f"""
def premature (d: Device) : Int :=
    let stream := default_stream d in
    let launch := launch_1d d 1 1 in
    let 1 left := upload_i32 d ({_int_array((1,))}) in
    let 1 right := upload_i32 d ({_int_array((2,))}) in
    let 1 pending := add_i32 launch stream left right in
    download_i32 pending;
"""
        + MAIN
    )
    errors = _errors(source)
    assert errors
    assert not any(isinstance(error, LinearityError) for error in errors), errors


# ---------------------------------------------------------------------------
# Refinement-protocol failures
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "body",
    [
        "let d := device (-1) in device_id d",
        "let d := default_device unit in let launch := launch_1d d (-1) 1 in launch_items launch",
        "let d := default_device unit in let launch := launch_1d d 0 1 in launch_items launch",
        "let d := default_device unit in let launch := launch_1d d 1 0 in launch_threads launch",
        "let d := default_device unit in let launch := launch_1d d 1 2 in launch_threads launch",
    ],
    ids=("negative-device", "negative-items", "zero-items", "zero-threads", "threads-above-items"),
)
def test_invalid_device_or_launch_dimensions_are_rejected(body: str):
    source = IMPORTS + f"def invalid (u: Unit) : Int := {body};" + MAIN
    assert _errors(source) != []


def test_threads_above_device_limit_are_rejected():
    source = (
        IMPORTS
        + """
def invalid (d: Device) (items: {n: Int | n > max_threads_per_block d}) : Launch1D :=
    launch_1d d items items;
"""
        + MAIN
    )
    assert _errors(source) != []


def test_empty_upload_is_rejected():
    source = (
        IMPORTS
        + """
def invalid (d: Device) : Unit :=
    let 1 buffer := upload_i32 d (Array.new{Int} unit) in
    free buffer;
"""
        + MAIN
    )
    assert _errors(source) != []


def test_add_rejects_unequal_vector_lengths():
    source = (
        IMPORTS
        + f"""
def invalid (d: Device) : Unit :=
    let stream := default_stream d in
    let launch := launch_1d d 2 2 in
    let 1 left := upload_i32 d ({_int_array((1, 2))}) in
    let 1 right := upload_i32 d ({_int_array((3,))}) in
    let 1 pending := add_i32 launch stream left right in
    discard pending;
"""
        + MAIN
    )
    assert _errors(source) != []


def test_add_rejects_launch_item_count_different_from_buffer_size():
    source = (
        IMPORTS
        + f"""
def invalid (d: Device) : Unit :=
    let stream := default_stream d in
    let launch := launch_1d d 1 1 in
    let 1 left := upload_i32 d ({_int_array((1, 2))}) in
    let 1 right := upload_i32 d ({_int_array((3, 4))}) in
    let 1 pending := add_i32 launch stream left right in
    discard pending;
"""
        + MAIN
    )
    assert _errors(source) != []


def test_add_rejects_cross_device_buffers():
    source = (
        IMPORTS
        + f"""
def invalid (u: Unit) : Unit :=
    let d0 := device 0 in
    let d1 := device 1 in
    let stream := default_stream d0 in
    let launch := launch_1d d0 1 1 in
    let 1 left := upload_i32 d0 ({_int_array((1,))}) in
    let 1 right := upload_i32 d1 ({_int_array((2,))}) in
    let 1 pending := add_i32 launch stream left right in
    discard pending;
"""
        + MAIN
    )
    assert _errors(source) != []


def test_cuda_vector_add_example_typechecks():
    example = Path(__file__).parents[1] / "examples" / "llvm" / "gpu" / "cuda_vector_add.ae"
    setup_logger()
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    assert AeonDriver(cfg).parse(filename=str(example)) == []


def test_cuda_download_example_typechecks():
    example = Path(__file__).parents[1] / "examples" / "llvm" / "gpu" / "cuda_download.ae"
    setup_logger()
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    assert AeonDriver(cfg).parse(filename=str(example)) == []
