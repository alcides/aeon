import numbers
import random
from collections.abc import Sequence
from typing import Any

from aeon.backend.evaluator import EvaluationContext
from aeon.core.terms import Hole
from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.sugar.lifting import lift
from aeon.synthesis.uis.api import PARETO_DISPLAY_LIMIT, SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name
from aeon.utils.pprint import pretty_print_sterm

# When fitness is a 5-vector from Image multi-objective examples (see libraries/Image.ae fitness_*).
_MULTIOBJ_LABELS = ("bw_mse", "half_mse", "rows_bad", "cols_bad", "pixels_bad")


def _format_quality(quality: Any) -> str:
    """Pretty-print fitness (object with fitness_components, or a raw numeric list)."""
    components: list[float] | None = None
    valid = True
    if hasattr(quality, "fitness_components"):
        components = list(quality.fitness_components)
        valid = bool(getattr(quality, "valid", True))
    elif isinstance(quality, list):
        components = [float(x) for x in quality]

    if components is not None and len(components) == len(_MULTIOBJ_LABELS):
        parts = [f"{lb}={v:.6g}" for lb, v in zip(_MULTIOBJ_LABELS, components)]
        suffix = "" if valid else " | INVALID (type/liquid check failed before numeric fitness)"
        return "[" + ", ".join(parts) + "]" + suffix
    if components is not None:
        return repr(components) + ("" if valid else " | INVALID")
    return repr(quality)


def _pretty_program(solution: Term | None) -> str:
    if solution is None:
        return "<none>"
    try:
        return pretty_print_sterm(lift(solution))
    except Exception:
        return str(solution)


def select_pareto_display(
    front: Sequence[tuple[Any, Term | None]],
    *,
    limit: int = PARETO_DISPLAY_LIMIT,
    rng: random.Random | None = None,
) -> list[tuple[Any, Term | None]]:
    """Return ``front`` unchanged, or ``limit`` randomly chosen members if larger."""
    items = list(front)
    if limit < 1 or len(items) <= limit:
        return items
    return (rng or random.Random()).sample(items, limit)


def format_pareto_front_lines(
    front: Sequence[tuple[Any, Term | None]],
    *,
    elapsed_time: float,
    budget: Any,
    limit: int = PARETO_DISPLAY_LIMIT,
    rng: random.Random | None = None,
) -> list[str]:
    """Build terminal lines describing the (possibly sampled) Pareto archive."""
    total = len(front)
    shown = select_pareto_display(front, limit=limit, rng=rng)
    if total > limit:
        header = f"# pareto t={elapsed_time:.1f}s/{budget}s size={total} (showing {len(shown)} of {total})"
    else:
        header = f"# pareto t={elapsed_time:.1f}s/{budget}s size={total}"
    lines = [header]
    for quality, term in shown:
        lines.append(f"#   {_format_quality(quality)}  {_pretty_program(term)}")
    return lines


class TerminalUI(SynthesisUI):
    """Plain-text synthesis feedback safe on Windows terminals (no progress bars or ANSI)."""

    best_solution: Term
    best_quality: list[float] | None

    def start(
        self,
        typing_ctx: TypingContext,
        evaluation_ctx: EvaluationContext,
        target_name: str,
        target_type: Type,
        budget: Any,
    ):
        self.target_name = target_name
        self.target_type = target_type
        self.budget = budget
        self.best_solution = Hole(Name("sorry", -1))
        self.best_quality = None
        self.pareto_front: list[tuple[Any, Term | None]] = []
        self._uses_front = False
        self._front_rng = random.Random(0)
        print(f"# Synthesizing ?{target_name} (budget={budget}s)", flush=True)

    def register(
        self,
        solution: Term,
        quality: Any,
        elapsed_time: float,
        is_best: bool,
    ):
        if not is_best:
            return
        self.best_solution = solution
        self.best_quality = quality
        # Pareto backends call ``register_front``; avoid a duplicate single-line
        # "best" that would hide the rest of the archive.
        if self._uses_front:
            return
        q_cur = _format_quality(quality)
        print(f"# best t={elapsed_time:.1f}s/{self.budget}s fitness {q_cur}", flush=True)

    def register_front(
        self,
        front: Sequence[tuple[Any, Term | None]],
        elapsed_time: float,
    ) -> None:
        self._uses_front = True
        self.pareto_front = list(front)
        if front:
            quality, term = front[-1]
            if term is not None:
                self.best_solution = term
            self.best_quality = quality
        for line in format_pareto_front_lines(
            front,
            elapsed_time=elapsed_time,
            budget=self.budget,
            rng=self._front_rng,
        ):
            print(line, flush=True)

    def end(self, solution: Term, quality: Any):
        if not (self._uses_front and self.pareto_front):
            return
        elapsed = float(self.budget) if isinstance(self.budget, numbers.Real) else 0.0
        lines = format_pareto_front_lines(
            self.pareto_front,
            elapsed_time=elapsed,
            budget=self.budget,
            rng=self._front_rng,
        )
        if lines:
            # Retitle the first line for the final dump.
            first = lines[0]
            if first.startswith("# pareto "):
                lines[0] = first.replace("# pareto ", "# final ", 1)
            for line in lines:
                print(line, flush=True)


class VerboseTerminalUI(TerminalUI):
    """Per-candidate synthesis log (can be noisy and slow on some terminals)."""

    def start(
        self,
        typing_ctx: TypingContext,
        evaluation_ctx: EvaluationContext,
        target_name: str,
        target_type: Type,
        budget: Any,
    ):
        self.target_name = target_name
        self.target_type = target_type
        self.budget = budget
        self.best_solution = Hole(Name("sorry", -1))
        self.best_quality = None
        self.pareto_front = []
        self._uses_front = False
        self._front_rng = random.Random(0)
        print(
            f"# Synthesis target: ?{target_name} :: {target_type} | "
            f"budget={budget}s | each line is one evaluated candidate; "
            f"pareto front dumps on archive updates.",
            flush=True,
        )
        if isinstance(budget, numbers.Real) and float(budget) >= 15:
            print(
                "# Five-objective Image runs label fitness as " + ", ".join(_MULTIOBJ_LABELS) + " (all minimized).",
                flush=True,
            )

    def register(
        self,
        solution: Term,
        quality: Any,
        elapsed_time: float,
        is_best: bool,
    ):
        if is_best:
            self.best_solution = solution
            self.best_quality = quality

        cur_pp = _pretty_program(solution)
        q_cur = _format_quality(quality)
        star = "*" if is_best else " "
        print(
            f"{star} t={elapsed_time:6.1f}s/{self.budget}s | fitness {q_cur}",
            flush=True,
        )
        print(cur_pp, flush=True)
        print("---", flush=True)
