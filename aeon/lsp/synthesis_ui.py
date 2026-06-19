"""A :class:`SynthesisUI` that streams live synthesis progress to the LSP
client as ``aeon/synthesisProgress`` notifications, so the editor (the Aeon
info view) can show, while a hole is being synthesized: the algorithm, how many
candidates were created / assessed, the best candidate(s) so far, and elapsed
time against the budget.

The notification payload is::

    {
      "hole": str,            # hole name
      "algorithm": str,       # readable synthesizer label
      "created": int,         # candidate programs generated so far
      "assessed": int,        # candidates evaluated/validated so far
      "best": str | None,     # pretty-printed best candidate so far
      "bestQuality": str | None,
      "elapsed": float,       # seconds since start
      "budget": float,        # time budget in seconds
      "done": bool,           # search finished
    }
"""

from __future__ import annotations

import time
from typing import Any, Optional

from aeon.backend.evaluator import EvaluationContext
from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.synthesis.uis.api import SynthesisUI

PROGRESS_NOTIFICATION = "aeon/synthesisProgress"
_THROTTLE_S = 0.12  # coalesce rapid updates so we don't flood the client


def _pretty(solution: Term | None) -> Optional[str]:
    if solution is None:
        return None
    try:
        from aeon.sugar.lifting import lift
        from aeon.utils.pprint import pretty_print_sterm

        return pretty_print_sterm(lift(solution))
    except Exception:
        try:
            return str(solution)
        except Exception:
            return None


def _quality(quality: Any) -> Optional[str]:
    if quality is None:
        return None
    try:
        if hasattr(quality, "fitness_components"):
            return repr(list(quality.fitness_components))
        return repr(quality)
    except Exception:
        return None


class LSPProgressUI(SynthesisUI):
    """Streams synthesis progress to ``ls`` for the hole being synthesized."""

    def __init__(self, ls: Any, synthesizer_name: str, hole_name: str):
        self._ls = ls
        # Readable label (e.g. "Finite Tree Automata (FTA)"); falls back to the id.
        from aeon.synthesis.modules.synthesizerfactory import synthesizer_label

        self._algorithm = synthesizer_label(synthesizer_name)
        self._hole = hole_name
        self._budget: float = 0.0
        self._created = 0
        self._assessed = 0
        self._best: Optional[str] = None
        self._best_quality: Optional[str] = None
        self._elapsed = 0.0
        self._last_send = 0.0
        # Once a backend reports richer counts via ``progress`` it owns them;
        # otherwise we count ``register`` calls (one per assessed candidate).
        self._counts_reported = False

    # -- SynthesisUI hooks ----------------------------------------------------

    def start(
        self,
        typing_ctx: Any,
        evaluation_ctx: EvaluationContext,
        target_name: str,
        target_type: Type | None,
        budget: Any,
    ):
        try:
            self._budget = float(budget)
        except (TypeError, ValueError):
            self._budget = 0.0
        self._send(force=True)

    def register(self, solution: Term, quality: Any, elapsed_time: float, is_best: bool):
        self._elapsed = elapsed_time
        if not self._counts_reported:
            # Each register is one assessed candidate; without richer reporting
            # we take created to track assessed.
            self._assessed += 1
            self._created = self._assessed
        if is_best and solution is not None:
            self._best = _pretty(solution)
            self._best_quality = _quality(quality)
        self._send()

    def progress(self, created: int, assessed: int, elapsed_time: float) -> None:
        self._counts_reported = True
        self._created = created
        self._assessed = assessed
        self._elapsed = elapsed_time
        self._send()

    def end(self, solution: Term, quality: Any):
        if solution is not None:
            best = _pretty(solution)
            if best is not None:
                self._best = best
                self._best_quality = _quality(quality)
        # Fill the bar to 100% on finish.
        self._elapsed = self._budget
        self._send(force=True, done=True)

    # -- notification ---------------------------------------------------------

    def _send(self, force: bool = False, done: bool = False) -> None:
        now = time.time()
        if not force and (now - self._last_send) < _THROTTLE_S:
            return
        self._last_send = now
        params = {
            "hole": self._hole,
            "algorithm": self._algorithm,
            "created": self._created,
            "assessed": self._assessed,
            "best": self._best,
            "bestQuality": self._best_quality,
            "elapsed": round(self._elapsed, 2),
            "budget": self._budget,
            "done": done,
        }
        try:
            self._notify(PROGRESS_NOTIFICATION, params)
        except Exception:
            # Never let progress reporting break synthesis.
            pass

    def _notify(self, method: str, params: Any) -> None:
        """Send a custom notification to the client. pygls 2.x exposes this as
        ``ls.protocol.notify``; older/test doubles may expose ``send_notification``
        directly, so fall back to it."""
        proto = getattr(self._ls, "protocol", None)
        if proto is not None and hasattr(proto, "notify"):
            proto.notify(method, params)
        else:
            self._ls.send_notification(method, params)
