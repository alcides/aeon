"""Synthesis backend family taxonomy."""

from __future__ import annotations

import pytest

from aeon.lsp.server import SYNTHESIZERS
from aeon.synthesis.modules.synthesizerfactory import (
    SYNTHESIZER_FAMILY_ORDER,
    SynthesizerFamily,
    is_known_synthesizer,
    sort_synthesizer_ids,
    synthesizer_family,
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


def test_sort_groups_by_family_then_label():
    ids = sort_synthesizer_ids(["gp", "llm", "enumerative", "random_search", "hc"])
    assert [synthesizer_family(i) for i in ids] == [
        SynthesizerFamily.GRAMMAR_SEARCH,
        SynthesizerFamily.GRAMMAR_SEARCH,
        SynthesizerFamily.METAHEURISTIC,
        SynthesizerFamily.METAHEURISTIC,
        SynthesizerFamily.LLM_ASSISTED,
    ]
