"""Exercise pipeline synthesis and held-out evaluation together."""

from pathlib import Path

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


pytest.importorskip("pandas")
pytest.importorskip("sklearn")

ROOT = Path(__file__).resolve().parents[1]


@pytest.mark.parametrize("case_name", ["hpo", "cv", "ensemble"])
def test_amltk_pipeline_is_synthesized_and_evaluated(case_name, monkeypatch):
    monkeypatch.chdir(ROOT)
    driver = AeonDriver(AeonConfig(synthesizer="random_search", synthesis_ui=SilentSynthesisUI(), synthesis_budget=2))
    errors = list(driver.parse(filename=str(ROOT / "examples" / "ml" / f"amltk_{case_name}.ae")))
    assert errors == []
    assert driver.has_synth()

    goals = [goal for entry in driver.metadata.values() for goal in entry.get("goals", [])]
    assert len(goals) == 1
    assert goals[0].minimize is False

    driver.synth()
    assert not driver.has_synth()
    accuracy = driver.run()
    assert isinstance(accuracy, float)
    assert 0.0 <= accuracy <= 1.0
