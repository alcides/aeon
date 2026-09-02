"""Forward-only and backward-only variants of the type-directed synthesizer.

`tdsyn_backward` expands holes only with the backward action (from the
expected type), `tdsyn_forward` only with the forward action (from the
variables in scope), while `tdsyn` / `tdsyn_enumerative` / `tdsyn_random`
keep combining both.
"""

from __future__ import annotations

import pytest

from aeon.core.types import t_int
from aeon.lsp.server import SYNTHESIZERS
from aeon.synthesis.modules.synthesizerfactory import (
    SynthesizerFamily,
    is_known_synthesizer,
    make_synthesizer,
    synthesizer_family,
    synthesizer_label,
)
from aeon.synthesis.modules.tdsyn import synthesizer as tdsyn_module
from aeon.synthesis.modules.tdsyn.synthesizer import TDSynSynthesizer
from aeon.synthesis.modules.tdsyn.worklist import PartialAST, TypedHole, fresh_hole
from aeon.typechecking.context import TypingContext

DIRECTIONAL_IDS = ["tdsyn_backward", "tdsyn_forward"]


# ---------------------------------------------------------------------------
# registration: ids, labels, families, LSP menu
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("backend", DIRECTIONAL_IDS)
def test_directional_backends_are_known(backend):
    assert is_known_synthesizer(backend)


def test_directional_backends_have_distinct_labels():
    assert synthesizer_label("tdsyn_backward") == "Type-directed synthesis (Backward only)"
    assert synthesizer_label("tdsyn_forward") == "Type-directed synthesis (Forward only)"


@pytest.mark.parametrize("backend", DIRECTIONAL_IDS)
def test_directional_backends_are_type_directed(backend):
    assert synthesizer_family(backend) == SynthesizerFamily.TYPE_DIRECTED


@pytest.mark.parametrize("backend", DIRECTIONAL_IDS)
def test_directional_backends_in_lsp_menu(backend):
    assert backend in SYNTHESIZERS


# ---------------------------------------------------------------------------
# make_synthesizer wiring
# ---------------------------------------------------------------------------


def test_make_synthesizer_backward():
    synth = make_synthesizer("tdsyn_backward")
    assert isinstance(synth, TDSynSynthesizer)
    assert synth.mode == "enumerative"
    assert synth.direction == "backward"


def test_make_synthesizer_forward():
    synth = make_synthesizer("tdsyn_forward")
    assert isinstance(synth, TDSynSynthesizer)
    assert synth.mode == "enumerative"
    assert synth.direction == "forward"


@pytest.mark.parametrize("backend", ["tdsyn", "tdsyn_enumerative", "tdsyn_random"])
def test_combined_backends_keep_both_directions(backend):
    synth = make_synthesizer(backend)
    assert isinstance(synth, TDSynSynthesizer)
    assert synth.direction == "both"


# ---------------------------------------------------------------------------
# expansion uses only the enabled action(s)
# ---------------------------------------------------------------------------


def _int_hole_partial() -> tuple[PartialAST, TypedHole]:
    hole_term, typed_hole = fresh_hole(t_int, TypingContext())
    return PartialAST(term=hole_term, holes=[typed_hole], depth=0), typed_hole


def _record_expansion_actions(synth: TDSynSynthesizer, monkeypatch) -> list[str]:
    calls: list[str] = []
    monkeypatch.setattr(tdsyn_module, "backward_candidates", lambda hole, skip: calls.append("backward") or [])
    monkeypatch.setattr(tdsyn_module, "forward_candidates", lambda hole, skip: calls.append("forward") or [])
    partial, typed_hole = _int_hole_partial()
    synth._expand_hole(partial, typed_hole, lambda name: False)
    return calls


def test_backward_only_expansion_skips_forward_action(monkeypatch):
    assert _record_expansion_actions(TDSynSynthesizer(direction="backward"), monkeypatch) == ["backward"]


def test_forward_only_expansion_skips_backward_action(monkeypatch):
    assert _record_expansion_actions(TDSynSynthesizer(direction="forward"), monkeypatch) == ["forward"]


def test_default_expansion_runs_both_actions(monkeypatch):
    assert _record_expansion_actions(TDSynSynthesizer(), monkeypatch) == ["backward", "forward"]


def test_backward_expansion_yields_candidates_for_int_hole():
    partial, typed_hole = _int_hole_partial()
    results = TDSynSynthesizer(direction="backward")._expand_hole(partial, typed_hole, lambda name: False)
    # Backward generates literals and if-then-else even in an empty context.
    assert results


def test_forward_expansion_is_empty_without_scope_variables():
    partial, typed_hole = _int_hole_partial()
    results = TDSynSynthesizer(direction="forward")._expand_hole(partial, typed_hole, lambda name: False)
    # Forward builds terms from variables in scope; an empty context has none.
    assert results == []
