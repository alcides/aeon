"""Tests for the LLM (Ollama) synthesis backend (``-s llm``, ``LLMSynthesizer``).

The backend prompts a local Ollama model, parses each response into an Aeon
expression, and returns the first candidate that type-checks against the hole.
The model call (``ollama.generate``) is the only external dependency, so it is
mocked here -- the tests exercise the parse/validate/retry loop deterministically
without contacting a server.
"""

from __future__ import annotations


import aeon.synthesis.modules.llm as llm
from aeon.core.terms import Literal
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.modules.llm import LLMSynthesizer, LLM_OLLAMA_MODELS, LLM_OPENAI_SYNTHESIZER_ID
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer

from tests.driver import check_and_return_core
from tests.synthesis_helpers import require_synthesized, synthesize_holes_or_skip


def _mock_generate(monkeypatch, responses):
    """Patch ``client.generate`` to yield ``responses`` in order, counting calls."""
    monkeypatch.setattr(llm, "prepare_ollama_model", lambda _model: None)
    monkeypatch.setattr(llm, "release_ollama_model", lambda _model: None)
    it = iter(responses)
    calls = {"n": 0}

    def fake(*, model=None, prompt=None, temperature=None, provider=None):
        calls["n"] += 1
        return next(it)

    monkeypatch.setattr(llm, "generate", fake)
    return calls


def _solve(code: str, budget: float = 5.0):
    term, ctx, ectx, metadata = check_and_return_core(code)
    targets = incomplete_functions_and_holes(ctx, term)
    holes = synthesize_holes_or_skip(ctx, ectx, term, targets, metadata, LLMSynthesizer(), budget=budget)
    return require_synthesized(holes[next(iter(holes))])


def test_factory_registers_llm():
    assert isinstance(make_synthesizer("llm"), LLMSynthesizer)
    assert make_synthesizer("llm").model == LLM_OLLAMA_MODELS["llm"]
    assert make_synthesizer("llm").provider == "ollama"


def test_factory_registers_per_model_llm_backends():
    syn = make_synthesizer("llm_qwen2.5-coder-14b")
    assert isinstance(syn, LLMSynthesizer)
    assert syn.model == "qwen2.5-coder:14b"
    assert syn.provider == "ollama"


def test_factory_registers_openai_llm_backend(monkeypatch):
    monkeypatch.setenv("AEON_LLM_MODEL", "gpt-4o")
    syn = make_synthesizer(LLM_OPENAI_SYNTHESIZER_ID)
    assert isinstance(syn, LLMSynthesizer)
    assert syn.model == "gpt-4o"
    assert syn.provider == "openai"


def test_openai_provider_skips_ollama_lifecycle(monkeypatch):
    monkeypatch.setenv("AEON_LLM_PROVIDER", "openai")
    monkeypatch.setenv("AEON_LLM_MODEL", "gpt-4o-mini")
    prepare_called = {"n": 0}
    release_called = {"n": 0}
    monkeypatch.setattr(
        llm, "prepare_ollama_model", lambda _model: prepare_called.__setitem__("n", prepare_called["n"] + 1)
    )
    monkeypatch.setattr(
        llm, "release_ollama_model", lambda _model: release_called.__setitem__("n", release_called["n"] + 1)
    )
    _mock_generate(monkeypatch, ["3"])
    t = _solve("def n : {x:Int | x = 3} := ?hole;")
    assert isinstance(t, Literal) and t.value == 3
    assert prepare_called["n"] == 0
    assert release_called["n"] == 0


def test_synthesizes_mocked_candidate(monkeypatch):
    calls = _mock_generate(monkeypatch, ["3"])
    t = _solve("def n : {x:Int | x = 3} := ?hole;")
    assert isinstance(t, Literal) and t.value == 3
    assert calls["n"] == 1


def test_synthesizes_plain_typed_hole(monkeypatch):
    _mock_generate(monkeypatch, ["7"])
    t = _solve("def n : Int := ?hole;")
    assert isinstance(t, Literal) and t.value == 7


def test_recovers_from_unparseable_response(monkeypatch):
    # A malformed first response must not crash the loop; the next valid one wins.
    calls = _mock_generate(monkeypatch, ["this is not aeon code !!!", "3"])
    t = _solve("def n : {x:Int | x = 3} := ?hole;")
    assert isinstance(t, Literal) and t.value == 3
    assert calls["n"] == 2
