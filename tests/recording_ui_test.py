import json

from aeon.core.terms import Literal
from aeon.core.types import t_int
from aeon.synthesis.uis.api import SynthesisFormat
from aeon.synthesis.uis.recording import RecordingUI


def test_results_without_start_are_recorded(tmp_path):
    path = tmp_path / "events.jsonl"
    ui = RecordingUI(path)
    ui.display_results(Literal(0, t_int), {}, SynthesisFormat.JSON)
    event = json.loads(path.read_text())
    assert event["event"] == "results"
    assert event["holes"] == {}
    assert event["wall_s"] >= 0


def test_progress_best_front_and_end_before_start(tmp_path):
    path = tmp_path / "events.jsonl"
    ui = RecordingUI(path)
    term = Literal(0, t_int)
    ui.progress(1, 1, 0.1)
    ui.register(term, [0.0], 0.1, True)
    ui.register_front([([0.0], term)], 0.1)
    ui.end(term, [0.0])
    events = [json.loads(line) for line in path.read_text().splitlines()]
    assert {"progress", "best", "front", "end"} <= {event["event"] for event in events}
    assert all(event["wall_s"] >= 0 for event in events)
