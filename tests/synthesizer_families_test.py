"""Synthesis backend family taxonomy."""

from __future__ import annotations

import pytest

from aeon.lsp.server import SYNTHESIZERS
from aeon.synthesis.modules.synthesizerfactory import (
    SYNTHESIZER_ALIASES,
    SYNTHESIZER_FAMILIES,
    SYNTHESIZER_FAMILY_ORDER,
    SYNTHESIZER_LABELS,
    _BUILTIN_SYNTHESIZER_IDS,
    SynthesizerFamily,
    is_known_synthesizer,
    sort_synthesizer_ids,
    synthesizer_family,
    synthesizer_menu_ids,
    validate_synthesizer,
)
from aeon.synthesis.api import UnknownSynthesizerError


def test_every_lsp_synthesizer_has_a_family():
    for module in SYNTHESIZERS:
        assert is_known_synthesizer(module)
        assert synthesizer_family(module) in SYNTHESIZER_FAMILY_ORDER


def test_unknown_synthesizer_raises():
    with pytest.raises(UnknownSynthesizerError, match="Unknown synthesizer: no_such_backend"):
        validate_synthesizer("no_such_backend")


def test_menu_covers_the_factory_registry_without_duplicate_aliases():
    from aeon.synthesis.modules.llm.ids import llm_synthesizer_menu_ids

    registered = _BUILTIN_SYNTHESIZER_IDS | set(llm_synthesizer_menu_ids()) | {"llm"}
    assert set(SYNTHESIZER_LABELS) == registered
    assert set(SYNTHESIZER_FAMILIES) == registered
    assert set(synthesizer_menu_ids()) == registered - SYNTHESIZER_ALIASES.keys()
    assert SYNTHESIZERS == synthesizer_menu_ids()
    assert len(SYNTHESIZERS) == len(set(SYNTHESIZERS))
    for alias, canonical in SYNTHESIZER_ALIASES.items():
        assert is_known_synthesizer(alias)
        assert canonical in SYNTHESIZERS


def test_registering_an_algorithm_exposes_it_in_menus(monkeypatch):
    from aeon.synthesis.modules import synthesizerfactory as factory

    monkeypatch.setattr(factory, "_BUILTIN_SYNTHESIZER_IDS", _BUILTIN_SYNTHESIZER_IDS | {"future_backend"})
    assert "future_backend" in synthesizer_menu_ids()


def test_sort_groups_by_family_then_label():
    ids = sort_synthesizer_ids(["gp", "llm", "enumerative", "random_search"])
    assert [synthesizer_family(i) for i in ids] == [
        SynthesizerFamily.GRAMMAR_SEARCH,
        SynthesizerFamily.GRAMMAR_SEARCH,
        SynthesizerFamily.METAHEURISTIC,
        SynthesizerFamily.LLM_ASSISTED,
    ]
