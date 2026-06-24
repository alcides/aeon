"""Tests for the LLM (Ollama) synthesis backend (``-s llm``, ``LLMSynthesizer``).

The backend prompts a local Ollama model, parses each response into an Aeon
expression, and returns the first candidate that type-checks against the hole.
The model call (``ollama.generate``) is the only external dependency, so it is
mocked here -- the tests exercise the parse/validate/retry loop deterministically
without contacting a server.
"""

from __future__ import annotations

import types


import aeon.synthesis.modules.llm as llm
from aeon.core.terms import Literal
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.modules.llm import LLMSynthesizer
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer

from tests.driver import check_and_return_core


def _mock_generate(monkeypatch, responses):
    """Patch ``ollama.generate`` to yield ``responses`` in order, counting calls."""
    it = iter(responses)
    calls = {"n": 0}

    def fake(model=None, prompt=None, options=None):
        calls["n"] += 1
        return types.SimpleNamespace(response=next(it))

    monkeypatch.setattr(llm, "generate", fake)
    return calls


def _solve(code: str, budget: float = 5.0):
    term, ctx, ectx, metadata = check_and_return_core(code)
    targets = incomplete_functions_and_holes(ctx, term)
    holes = synthesize_holes(ctx, ectx, term, targets, metadata, LLMSynthesizer(), budget=budget)
    return holes[next(iter(holes))]


def test_factory_registers_llm():
    assert isinstance(make_synthesizer("llm"), LLMSynthesizer)


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
