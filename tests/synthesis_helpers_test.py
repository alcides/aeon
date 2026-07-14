"""Tests for synthesis test helpers."""

from __future__ import annotations

import pytest

from aeon.core.terms import Hole
from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.utils.name import Name
from tests.synthesis_helpers import require_synthesized, synthesize_holes_or_skip


def test_require_synthesized_skips_on_hole():
    with pytest.raises(pytest.skip.Exception, match="did not fill"):
        require_synthesized(Hole(Name("h", 0)))


def test_require_synthesized_skips_on_none():
    with pytest.raises(pytest.skip.Exception, match="did not fill"):
        require_synthesized(None)


def test_synthesize_holes_or_skip_skips_on_budget(monkeypatch):
    def boom(*_args, **_kwargs):
        raise SynthesisNotSuccessful("SynquidSynthesizer: no valid candidate found within budget")

    monkeypatch.setattr("tests.synthesis_helpers._synthesize_holes", boom)
    with pytest.raises(pytest.skip.Exception, match="within budget"):
        synthesize_holes_or_skip()
