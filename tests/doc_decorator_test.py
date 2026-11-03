"""Documentation annotations feed compilation metadata and HTML generation."""

from __future__ import annotations

import subprocess
import sys

import pytest

from aeon.documentation.generator import extract_documentation, generate_html
from aeon.errors import InvalidDecoratorArgumentError, UnknownDecoratorError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI
from tests.driver import check_and_return_core


def test_doc_is_attached_to_the_correct_definition():
    _, _, _, metadata = check_and_return_core(
        '@doc("First description.")\ndef first : Int := 1;\n@doc("Second description.")\ndef second : Int := 2;'
    )
    assert {name.name: data["doc"] for name, data in metadata.items() if "doc" in data} == {
        "first": "First description.",
        "second": "Second description.",
    }
    assert all("prompt" not in data for data in metadata.values())


@pytest.mark.parametrize("doc_first", [True, False])
def test_doc_text_renders_with_arguments_and_examples(doc_first):
    annotation = r'@doc("Use <x> & \"quotes\".\nx: Input integer.\nreturns: Incremented value.")'
    example = "@example(inc 1 = 2)"
    annotations = [annotation, example] if doc_first else [example, annotation]
    source = "type Marker\n\n# Old description.\n" + "\n".join(annotations) + "\ndef inc (x:Int) : Int := x + 1;"
    document = extract_documentation("inline.ae", source)
    function = document.functions[0]
    assert function.comment == 'Use <x> & "quotes".'
    assert function.arg_docs == {"x": "Input integer."}
    assert function.return_doc == "Incremented value."
    assert function.examples == ["inc 1 = 2"]
    assert function.decorators == []
    rendered = generate_html(document)
    assert "Use &lt;x&gt; &amp; &quot;quotes&quot;." in rendered
    assert "Old description." not in rendered
    assert "Input integer." in rendered
    assert "Incremented value." in rendered
    assert "inc 1 = 2" in rendered


def test_comments_remain_the_fallback_and_empty_doc_overrides_them():
    source = """type Marker

# Comment documentation.
# x: A number.
# returns: The same number.
def identity (x:Int) : Int := x;

# Hidden description.
@doc("")
def empty : Int := 0;
"""
    identity, empty = extract_documentation("inline.ae", source).functions
    assert identity.comment == "Comment documentation."
    assert identity.arg_docs == {"x": "A number."}
    assert identity.return_doc == "The same number."
    assert empty.comment is None


@pytest.mark.parametrize("annotation", ["@doc", "@doc(42)", "@doc(true)", '@doc("one", "two")'])
def test_invalid_doc_is_rejected_by_compilation_and_documentation(annotation):
    source = f"{annotation}\ndef value : Int := 1;"
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), synthesis_budget=1, no_main=True))
    errors = list(driver.parse(aeon_code=source))
    assert any(isinstance(e, InvalidDecoratorArgumentError) for e in errors), errors
    assert "expected exactly one string literal" in str(errors[0])
    with pytest.raises(InvalidDecoratorArgumentError, match="expected exactly one string literal"):
        extract_documentation("inline.ae", source)


def test_prompt_has_been_replaced():
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), synthesis_budget=1, no_main=True))
    errors = list(driver.parse(aeon_code='@prompt("Old annotation")\ndef value : Int := 1;'))
    assert any(isinstance(e, UnknownDecoratorError) for e in errors), errors


@pytest.mark.parametrize("valid", [True, False])
def test_doc_cli(tmp_path, valid):
    source = tmp_path / "documented.ae"
    source.write_text(
        '@doc("Documented by annotation.")\ndef value : Int := 1;' if valid else "@doc(42)\ndef value : Int := 1;"
    )
    output = tmp_path / "documentation.html"
    result = subprocess.run(
        [sys.executable, "-m", "aeon", "--doc", str(source), "--doc-output", str(output)],
        capture_output=True,
        text=True,
        timeout=30,
    )
    if valid:
        assert result.returncode == 0, result.stdout + result.stderr
        assert "Documented by annotation." in output.read_text()
    else:
        assert result.returncode != 0
        assert "expected exactly one string literal" in result.stdout + result.stderr
        assert "Traceback" not in result.stderr
        assert not output.exists()
