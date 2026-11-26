"""Impossible hypotheses warn without turning vacuous proofs into errors."""

import asyncio
import io
from pathlib import Path

import pytest
from lsprotocol.types import DiagnosticSeverity
from z3 import Solver, unknown

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.lsp import aeon_adapter
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.verification.false_parameters import collect_false_parameter_warnings


SOURCE = """def amazing
    (n:{v:Int | v >= 0})
    (h1:{p:Unit | n > 5})
    (h2:{p:Unit | n < 3})
    : {p:Unit | false} := unit;
"""
URI = "file:///contradictory-parameters.ae"


def compile_source(source, **options):
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 0, no_main=True, **options))
    assert not list(driver.parse(filename=URI, aeon_code=source))
    return driver


def analyse(source):
    aeon_adapter.clear_cache(URI)
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 0, no_main=True))
    return asyncio.run(aeon_adapter._parse(io.StringIO(source), driver, URI))


def test_lean_translation_typechecks_and_names_conflicting_hypotheses():
    driver = compile_source(SOURCE, strict_decidable=True)
    (warning,) = driver.false_parameter_warnings
    assert warning.parameters == ("h1", "h2")
    assert "contradictory" in warning.message and "vacuous" in warning.message
    assert warning.location.get_start()[0] == 4


def test_editor_warning_links_both_hypotheses():
    result = analyse(SOURCE)
    (warning,) = result.diagnostics
    assert warning.severity == DiagnosticSeverity.Warning
    assert warning.code == "contradictory-parameter-hypotheses"
    assert warning.data == {"kind": warning.code, "parameters": ["h1", "h2"]}
    assert warning.range.start.line == 3
    assert [info.location.range.start.line for info in warning.related_information] == [
        2,
        3,
    ]
    assert all(info.location.uri == URI for info in warning.related_information)


def test_example_file_warns_in_editor():
    source = (Path(__file__).resolve().parents[1] / "examples/vacuous_hypotheses.ae").read_text()
    result = analyse(source)
    assert len(result.diagnostics) == 1
    assert result.diagnostics[0].data["parameters"] == ["h1", "h2"]


@pytest.mark.parametrize("bound, impossible", [(3, True), (6, True), (7, False), (10, False)])
def test_integer_bounds(bound, impossible):
    # Result is satisfiable so both the vacuous and inhabited cases compile.
    source = SOURCE.replace("n < 3", f"n < {bound}").replace("{p:Unit | false}", "Unit")
    driver = compile_source(source)
    assert bool(driver.false_parameter_warnings) is impossible


@pytest.mark.parametrize(
    "source",
    [
        "def f (x:{v:Int | v > 5}) (y:{v:Int | v < 3}):Unit := unit;",
        "def f (x:{v:Int | v > 5}):Unit := unit; def g (x:{v:Int | v < 3}):Unit := unit;",
        "def f (x:{v:Bool | v = false}):Bool := x;",
        "def f (x:Int):{v:Int | v > 5} := 6;",
        "def f (g:(x:{v:Int | v > 5}) -> Int) (x:{v:Int | v < 3}):Unit := unit;",
    ],
)
def test_satisfiable_scopes_and_results_do_not_warn(source):
    assert not compile_source(source).false_parameter_warnings


def test_individually_impossible_refinement_warns():
    driver = compile_source("def f (x:{v:Int | v > 5 && v < 3}):Int := x;")
    (warning,) = driver.false_parameter_warnings
    assert warning.parameters == ("x",)


def test_edit_removes_stale_warning():
    assert analyse(SOURCE).diagnostics
    assert not analyse(SOURCE.replace("n < 3", "n < 8").replace("{p:Unit | false}", "Unit")).diagnostics


def test_unknown_is_not_a_contradiction(monkeypatch):
    driver = compile_source(SOURCE)
    monkeypatch.setattr(Solver, "check", lambda self, *args: unknown)
    with driver.session.activate():
        assert not collect_false_parameter_warnings(driver.core, source_path=URI)


def test_unsupported_predicates_do_not_crash_or_warn(monkeypatch):
    import aeon.verification.false_parameters as parameters

    driver = compile_source(SOURCE)

    def unsupported(*args):
        raise KeyError("unsupported symbol")

    monkeypatch.setattr(parameters, "translate_liq", unsupported)
    with driver.session.activate():
        assert not collect_false_parameter_warnings(driver.core, source_path=URI)


def test_advisory_queries_are_not_reported_as_program_obligations():
    from aeon.verification.trace import collect_verification

    driver = compile_source(SOURCE)
    with driver.session.activate(), collect_verification() as evidence:
        assert collect_false_parameter_warnings(driver.core, source_path=URI)
    assert not evidence


def test_other_source_file_does_not_receive_warning():
    driver = compile_source(SOURCE)
    with driver.session.activate():
        assert not collect_false_parameter_warnings(driver.core, source_path="file:///other.ae")
