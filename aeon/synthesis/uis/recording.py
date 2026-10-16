"""Reusable benchmark recording UI with bounded JSONL telemetry."""

import json
import os
import random
import time

from aeon.synthesis.uis.terminal import TerminalUI


def quality_data(q):
    components = getattr(q, "fitness_components", q)
    try:
        components = [float(x) for x in components]
    except (TypeError, ValueError):
        components = None
    return {"components": components, "valid": getattr(q, "valid", None), "raw": str(q)}


class RecordingUI(TerminalUI):
    """JSONL telemetry whose lifecycle is safe before an optional start call."""

    def __init__(self, events_path=None):
        self.events_path = events_path or os.environ.get("AEON_EVENTS")
        if self.events_path is None:
            raise ValueError("RecordingUI requires events_path or AEON_EVENTS")
        self.origin = time.monotonic()
        self.last_best_event = -1.0
        self.last_front_event = -1.0
        self.last_progress_event = -1.0
        self.perfect_emitted = False
        self.target_name = ""
        self.budget = 0
        self.best_solution = None
        self.best_quality = None
        self.pareto_front = []
        self._uses_front = False
        self._front_rng = random.Random(0)

    def emit(self, event, **data):
        with open(self.events_path, "a") as f:
            f.write(
                json.dumps(
                    {
                        "event": event,
                        "wall_s": time.monotonic() - self.origin,
                        "target": getattr(self, "target_name", None),
                        **data,
                    },
                    default=str,
                )
                + "\n"
            )

    def start(self, typing_ctx, evaluation_ctx, target_name, target_type, budget):
        self.origin = time.monotonic()
        self.last_best_event = -1.0
        self.last_front_event = -1.0
        self.last_progress_event = -1.0
        self.perfect_emitted = False
        super().start(typing_ctx, evaluation_ctx, target_name, target_type, budget)
        self.emit("start", goal_type=str(target_type), context=str(typing_ctx), budget=str(budget))

    def register(self, solution, quality, elapsed_time, is_best):
        interval = float(os.environ.get("AEON_EVENT_INTERVAL", "0"))
        if is_best and elapsed_time - self.last_best_event >= interval:
            self.emit("best", search_s=elapsed_time, quality=quality_data(quality), solution=str(solution))
            self.last_best_event = elapsed_time
        super().register(solution, quality, elapsed_time, is_best)

    def progress(self, created, assessed, elapsed_time):
        interval = float(os.environ.get("AEON_EVENT_INTERVAL", "0"))
        if elapsed_time - self.last_progress_event >= interval:
            self.emit("progress", created=created, assessed=assessed, search_s=elapsed_time)
            self.last_progress_event = elapsed_time

    def register_front(self, front, elapsed_time):
        limit = int(os.environ.get("AEON_EVENT_FRONT_LIMIT", str(len(front))))
        interval = float(os.environ.get("AEON_EVENT_INTERVAL", "0"))
        for q, term in front:
            data = quality_data(q)
            if (
                data["components"]
                and all(x == 0 for x in data["components"])
                and data["valid"] is not False
                and not self.perfect_emitted
            ):
                self.emit("training_perfect", search_s=elapsed_time, quality=data, solution=str(term))
                self.perfect_emitted = True
        if elapsed_time - self.last_front_event >= interval:
            self.emit(
                "front",
                search_s=elapsed_time,
                front_size=len(front),
                front=[{"quality": quality_data(q), "solution": str(t)} for q, t in list(front)[:limit]],
            )
            self.last_front_event = elapsed_time
        if os.environ.get("AEON_QUIET_PROGRESS") == "1":
            self._uses_front = True
            self.pareto_front = list(front)
            if front:
                self.best_quality, self.best_solution = front[-1]
        else:
            super().register_front(front, elapsed_time)

    def end(self, solution, quality):
        self.emit("end", quality=quality_data(quality), solution=str(solution))
        if os.environ.get("AEON_QUIET_PROGRESS") != "1":
            super().end(solution, quality)

    def display_results(self, program, terms, synthesis_format):
        self.emit("results", holes={str(k): str(v) for k, v in terms.items()})
        super().display_results(program, terms, synthesis_format)
