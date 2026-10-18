"""Run Aeon's CLI with structured synthesis UI telemetry (source stays untouched)."""

import json
import os
import sys
import time

sys.path.insert(0, os.environ["AEON_SOURCE"])
from monotonicity_worker import is_monotonicity_case, main as monotonicity_main

if __name__ == "__main__" and len(sys.argv) > 1 and is_monotonicity_case(os.environ["AEON_SOURCE"], sys.argv[-1]):
    raise SystemExit(monotonicity_main(sys.argv[1:], os.environ["AEON_EVENTS"]))

if os.environ.get("AEON_PSB2_SAMPLES"):
    from psb2_cached import install

    install(os.environ["AEON_PSB2_SAMPLES"])
from aeon.synthesis.uis.terminal import TerminalUI
import aeon.__main__ as cli


def quality_data(q):
    components = getattr(q, "fitness_components", q)
    try:
        components = [float(x) for x in components]
    except (TypeError, ValueError):
        components = None
    return {"components": components, "valid": getattr(q, "valid", None), "raw": str(q)}


class RecordingUI(TerminalUI):
    def __init__(self):
        self.origin = time.monotonic()

    def emit(self, event, **data):
        with open(os.environ["AEON_EVENTS"], "a") as f:
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


cli.select_synthesis_ui = lambda verbose=False: RecordingUI()
if __name__ == "__main__":
    cli.main()
