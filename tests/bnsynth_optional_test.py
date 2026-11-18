"""Registration and dependency errors work without installing PyTorch."""

import sys

import pytest

from aeon.lsp.server import SYNTHESIZERS
from aeon.synthesis.api import UnsupportedSynthesisGoal
from aeon.synthesis.modules.bnsynth import BNSynthSynthesizer
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from tests.joint_hole_synthesis_test import parse, solve


def test_neural_backend_is_available_in_cli_and_lsp():
    assert isinstance(make_synthesizer("bnsynth"), BNSynthSynthesizer)
    assert "bnsynth" in SYNTHESIZERS


def test_missing_torch_has_actionable_capability_error(monkeypatch):
    driver = parse("@bounded_cnf(0) def f:Bool := ?h;")
    monkeypatch.setitem(sys.modules, "torch", None)
    backend = BNSynthSynthesizer()
    with pytest.raises(UnsupportedSynthesisGoal, match="synthesis-bnsynth"):
        solve(driver, backend, budget=3)
    assert backend.report.status == "unsupported"
