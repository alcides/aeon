"""Verification evidence is current, source-located, and not guessed from bools."""

import asyncio
import io
import json
from types import SimpleNamespace

import pytest
from lsprotocol.types import HoverParams, Position, TextDocumentIdentifier
from z3 import Solver, unknown

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.lsp import aeon_adapter
from aeon.lsp.server import AeonLanguageServer, VERIFICATION_REQUEST
from aeon.lsp.verification import obligations_at, proof_obligations
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.verification import smt
from aeon.verification.helpers import parse_liquid
from aeon.verification.trace import collect_verification
from aeon.verification.vcs import LiquidConstraint
from aeon.utils.location import FileLocation


URI = "file:///lsp-verification.ae"


def driver(contracts=False):
    return AeonDriver(AeonConfig("gp", SilentSynthesisUI(), 1, contracts=contracts))


def analyse(source, contracts=False, uri=URI):
    aeon_adapter.clear_cache(uri)
    result = asyncio.run(aeon_adapter._parse(io.StringIO(source), driver(contracts), uri))
    return result, aeon_adapter.get_proof_obligations(uri)


def test_accepted_refinement_has_located_proof():
    source = "def inc (x:Int) : {v:Int | v > x} := x + 1;"
    result, proofs = analyse(source)
    assert not result.diagnostics
    assert proofs and all(p["status"] == "valid" for p in proofs)
    selected = obligations_at(proofs, 0, source.index("x + 1"))
    assert selected and ">" in selected[0]["obligation"]
    assert selected[0]["counterexample"] is None
    json.dumps(proofs)


def test_each_accepted_definition_has_its_own_obligation():
    source = "def a (x:Int) : {v:Int | v > x} := x + 1;\ndef b (x:Int) : {v:Int | v < x} := x - 1;"
    result, proofs = analyse(source)
    assert not result.diagnostics
    assert obligations_at(proofs, 0, source.splitlines()[0].index("x + 1"))
    assert obligations_at(proofs, 1, source.splitlines()[1].index("x - 1"))


def test_failed_program_does_not_blame_its_first_valid_definition():
    source = "def a (x:Int) : {v:Int | v > x} := x + 1;\ndef b (x:Int) : {v:Int | v > 0} := x;"
    result, proofs = analyse(source)
    assert result.diagnostics
    good = obligations_at(proofs, 0, source.splitlines()[0].index("x + 1"))
    assert good and all(p["status"] == "valid" for p in good)
    bad = obligations_at(proofs, 1, source.splitlines()[1].index(":= x") + 3)
    assert any(p["status"] == "invalid" for p in bad)


def test_rejected_refinement_has_counterexample_and_diagnostic_data():
    result, proofs = analyse("def bad (x:Int) : {v:Int | v > 0} := x;")
    diag = next(d for d in result.diagnostics if d.code == "refinement")
    assert diag.data["status"] == "invalid"
    assert diag.data["counterexample"] is not None
    assert any(p["status"] == "invalid" and p["counterexample"] for p in proofs)


def test_proof_evidence_cleared_on_syntax_error_and_document_change():
    analyse("def inc (x:Int) : {v:Int | v > x} := x + 1;")
    assert aeon_adapter.get_proof_obligations(URI)
    result, proofs = analyse("def inc :")
    assert result.diagnostics and not proofs
    aeon_adapter.clear_cache(URI)
    assert aeon_adapter.get_proof_obligations(URI) == []


def test_documents_do_not_share_evidence():
    analyse("def inc (x:Int) : {v:Int | v > x} := x + 1;", uri="file:///good.ae")
    analyse("def bad (x:Int) : {v:Int | v > x} := x - 1;", uri="file:///bad.ae")
    assert all(p["status"] == "valid" for p in aeon_adapter.get_proof_obligations("file:///good.ae"))
    assert any(p["status"] == "invalid" for p in aeon_adapter.get_proof_obligations("file:///bad.ae"))


def test_imported_native_definitions_do_not_warn_at_local_positions():
    result, proofs = analyse("import Math;\ndef inc (x:Int) : {v:Int | v > x} := x + 1;")
    assert not [d for d in result.diagnostics if d.code == "runtime-verification"]
    assert proofs and all(p["range"] is None or p["range"]["start"]["line"] == 1 for p in proofs)


@pytest.mark.parametrize("enabled", [False, True])
def test_native_warning_reports_runtime_mode_without_running_code(enabled):
    result, _ = analyse('def bad (x:Int) : {v:Int | v >= 0} := native "1 / 0";', contracts=enabled)
    warning = next(d for d in result.diagnostics if d.code == "runtime-verification")
    assert warning.data == {"kind": "runtime-verification", "enabled": enabled, "executed": False}
    assert "not statically verified" in warning.message
    assert warning.range.start.character > 0


def test_unknown_is_not_invalid_even_on_cache_hit(monkeypatch):
    constraint = LiquidConstraint(parse_liquid("93217 == 93218"), loc=FileLocation(URI, (1, 1), (1, 10)))
    smt.clear_smt_caches()
    monkeypatch.setattr(Solver, "check", lambda self: unknown)
    monkeypatch.setattr(Solver, "reason_unknown", lambda self: "test timeout")
    with collect_verification() as evidence:
        assert not smt.smt_valid(constraint)
        assert not smt.smt_valid(constraint)
    assert [e.status for e in evidence] == ["unknown", "unknown"]
    assert evidence[1].cached and evidence[1].reason == "test timeout"
    proofs = proof_obligations(evidence)
    assert proofs[0]["counterexample"] is None
    smt.clear_smt_caches()


def test_unknown_diagnostic_does_not_offer_counterexample(monkeypatch):
    monkeypatch.setattr(Solver, "check", lambda self: unknown)
    monkeypatch.setattr(Solver, "reason_unknown", lambda self: "test timeout")
    result, proofs = analyse("def bad (x:Int) : {v:Int | v > x} := x - 1;")
    assert proofs and all(p["status"] == "unknown" for p in proofs)
    diag = next(d for d in result.diagnostics if d.code == "refinement")
    assert diag.data["status"] == "unknown" and diag.data["counterexample"] is None
    smt.clear_smt_caches()


def test_undefined_translation_is_unsupported_not_disproved(monkeypatch):
    constraint = LiquidConstraint(parse_liquid("(1 / 0) == 3"), loc=FileLocation(URI, (1, 1), (1, 10)))
    smt.clear_smt_caches()

    def undefined(*args):
        raise ZeroDivisionError

    monkeypatch.setattr(smt, "translate", undefined)
    with collect_verification() as evidence:
        assert not smt.smt_valid(constraint)
    assert evidence[0].status == "unsupported"
    assert "zero" in evidence[0].reason
    assert proof_obligations(evidence)[0]["counterexample"] is None


def test_nested_collectors_are_isolated_and_restored():
    constraint = LiquidConstraint(parse_liquid("true"))
    with collect_verification() as outer:
        with collect_verification() as inner:
            smt.smt_valid(constraint)
        assert len(inner) == 1 and not outer
        smt.smt_valid(constraint)
    assert len(outer) == 1


def test_horn_assignment_does_not_publish_exploratory_failures(monkeypatch):
    from aeon.verification import horn

    constraint = LiquidConstraint(parse_liquid("false"))

    def exploratory(*args):
        smt.smt_valid(constraint)
        return {}

    monkeypatch.setattr(horn, "fixpoint", exploratory)
    with collect_verification() as evidence:
        horn.horn_assignment(constraint)
        assert not evidence
        smt.smt_valid(constraint)
    assert len(evidence) == 1 and evidence[0].status == "invalid"


@pytest.mark.parametrize(
    "source, status",
    [
        ("def inc (x:Int) : {v:Int | v > x} := x + 1;", "valid"),
        ("def positive (x:Int) : {v:Int | v > 0} := x;", "invalid"),
    ],
)
def test_real_server_hover_and_custom_request(source, status):
    from lsprotocol.types import TEXT_DOCUMENT_HOVER, TextDocumentItem
    from aeon.lsp.server import INFOVIEW_REQUEST
    from pygls.workspace import Workspace

    ls = AeonLanguageServer(driver())
    ls.protocol._workspace = Workspace(None)
    ls.workspace.put_text_document(TextDocumentItem(uri=URI, language_id="aeon", version=1, text=source))
    aeon_adapter.clear_cache(URI)
    hover = ls.protocol.fm.features[TEXT_DOCUMENT_HOVER]
    result = asyncio.run(
        hover(HoverParams(text_document=TextDocumentIdentifier(URI), position=Position(0, source.index(":= x") + 3)))
    )
    assert f"Verification: **{status}**" in result.contents.value
    assert "Int" in result.contents.value
    handler = ls.protocol.fm.features[VERIFICATION_REQUEST]
    payload = asyncio.run(handler(SimpleNamespace(textDocument=SimpleNamespace(uri=URI))))
    assert payload["obligations"] and payload["runtimeVerification"]["executed"] is False
    json.dumps(payload)
    info_handler = ls.protocol.fm.features[INFOVIEW_REQUEST]
    info = asyncio.run(
        info_handler(
            SimpleNamespace(
                textDocument=SimpleNamespace(uri=URI),
                position=SimpleNamespace(line=0, character=source.index(":= x") + 3),
            )
        )
    )
    assert info["proofObligations"] == payload["obligations"]
    assert "target" in info and "errors" in info
    json.dumps(info)
