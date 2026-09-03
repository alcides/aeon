"""Tests for AeonDoc extraction of linear types and multiplicities."""

from __future__ import annotations

from aeon.documentation.generator import extract_documentation, generate_html


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
    assert upload.args[1][2] == ""

    html = generate_html(doc)
    assert "badge badge-linear" in html
    assert ">linear</span>" in html
    assert "linear type ReadyBuffer" in html
    assert "(1 values:" in html
    assert "(device:" in html


def test_array_module_marks_array_linear():
    doc = extract_documentation("aeon/libraries/Array.ae")
    array = next(t for t in doc.types if t.name == "Array")
    assert array.is_linear is True
    append = next(f for f in doc.functions if f.name == "append")
    assert append.args[0][2] == "1 "
