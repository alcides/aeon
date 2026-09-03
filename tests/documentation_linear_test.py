"""Tests for AeonDoc extraction of linear types and multiplicities."""

from __future__ import annotations

from aeon.documentation.generator import extract_documentation, generate_html
from aeon.sugar.parser import parse_type
from aeon.utils.name import Name
from aeon.utils.pprint import pretty_print_param, pretty_print_stype


def test_linear_type_flag_and_badge_in_html():
    source = """
# A unique buffer.
linear type ReadyBuffer a

type Device

# Upload consumes the host array.
def upload (1 values: (Array Int)) (device: Device) : (ReadyBuffer Int) :=
    native "None"
"""
    doc = extract_documentation("<test>", source)
    by_name = {t.name: t for t in doc.types}
    assert by_name["ReadyBuffer"].is_linear is True
    assert by_name["Device"].is_linear is False

    upload = next(f for f in doc.functions if f.name == "upload")
    assert upload.args[0][0] == "values"
    assert upload.args[0][2] == "1 "
    assert "(1 values :" in upload.args[0][1] or "(1 values:" in upload.args[0][1]
    assert upload.args[1][2] == ""

    html = generate_html(doc)
    assert "badge badge-linear" in html
    assert ">linear</span>" in html
    assert "linear type ReadyBuffer" in html
    assert "(1 values" in html
    assert "(device" in html


def test_pretty_printer_inlines_refined_param_binder():
    ty = parse_type("{n: Int | n >= 0 && n < 10}")
    rendered = pretty_print_param(Name("id", 0), ty)
    assert rendered.startswith("(id : Int |")
    assert "id ≥ 0" in rendered
    assert "n ≥ 0" not in rendered
    # Bare refined types (no named binder context) keep braces.
    assert pretty_print_stype(ty).startswith("{n : Int |") or pretty_print_stype(ty).startswith("{n: Int |")


def test_refined_param_binder_aligned_to_arg_name():
    source = """
type Device
def num_devices (_: Unit) : Int := native "1"
def device_id : (d: Device) -> Int := uninterpreted
def max_threads_per_block : (d: Device) -> Int := uninterpreted
def device (id: {n: Int | n >= 0 && n < num_devices unit}) :
    {d: Device | device_id d = id && max_threads_per_block d > 0} :=
    native "None"
"""
    doc = extract_documentation("<test>", source)
    device = next(f for f in doc.functions if f.name == "device")
    pretty_param = device.args[0][1]
    assert pretty_param.startswith("(id : Int |")
    assert "id ≥ 0" in pretty_param
    assert "n ≥ 0" not in pretty_param
    # Return type keeps brace form with its own binder.
    assert device.type_sig.startswith("{d : Device |") or device.type_sig.startswith("{d: Device |")

    html = generate_html(doc)
    assert "(id : Int |" in html


def test_array_module_marks_array_linear():
    doc = extract_documentation("aeon/libraries/Array.ae")
    array = next(t for t in doc.types if t.name == "Array")
    assert array.is_linear is True
    append = next(f for f in doc.functions if f.name == "append")
    assert append.args[0][2] == "1 "
