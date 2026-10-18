"""Final program results do not require a per-target search to have started."""

import json
from pathlib import Path
import runpy

import pytest

from aeon.backend.evaluator import EvaluationContext
from aeon.core.terms import Literal
from aeon.core.types import t_int
from aeon.synthesis.uis.api import SynthesisFormat
from aeon.typechecking.context import TypingContext


@pytest.fixture
def recording_worker(monkeypatch, tmp_path):
    import aeon.__main__ as cli

    root = Path(__file__).resolve().parents[3]
    script = Path(__file__).resolve().parents[1] / "scripts/worker.py"
    events = tmp_path / "events.jsonl"
    monkeypatch.setenv("AEON_SOURCE", str(root))
    monkeypatch.setenv("AEON_EVENTS", str(events))
    monkeypatch.delenv("AEON_PSB2_SAMPLES", raising=False)
    monkeypatch.syspath_prepend(str(script.parent))
    # The wrapper installs its UI factory; restore the CLI after each test.
    monkeypatch.setattr(cli, "select_synthesis_ui", cli.select_synthesis_ui)
    worker = runpy.run_path(str(script))
    return worker, events


def test_final_results_without_search_start(recording_worker):
    worker, path = recording_worker
    ui = worker["RecordingUI"]()
    ui.display_results(Literal(0, t_int), {}, SynthesisFormat.JSON)
    event = json.loads(path.read_text())
    assert event["event"] == "results"
    assert event["holes"] == {}
    assert event["target"] is None
    assert event["wall_s"] >= 0


def test_timestamps_remain_relative_to_run_start(recording_worker, monkeypatch):
    worker, path = recording_worker
    clock = [100.0]
    monkeypatch.setattr(worker["time"], "monotonic", lambda: clock[0])
    ui = worker["RecordingUI"]()
    for now, target in [(102.0, "first"), (105.0, "second")]:
        clock[0] = now
        ui.start(TypingContext(), EvaluationContext(), target, t_int, 5)
    clock[0] = 106.0
    ui.display_results(Literal(0, t_int), {}, SynthesisFormat.JSON)
    events = [json.loads(line) for line in path.read_text().splitlines()]
    assert [event["event"] for event in events] == ["start", "start", "results"]
    assert [event["wall_s"] for event in events] == [2.0, 5.0, 6.0]
    assert [event["target"] for event in events] == ["first", "second", "second"]
