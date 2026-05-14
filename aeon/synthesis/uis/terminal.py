import numbers
from typing import Any

from aeon.backend.evaluator import EvaluationContext
from aeon.core.terms import Hole
from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.sugar.lifting import lift
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name
from aeon.utils.pprint import pretty_print_sterm

# When fitness is a 5-vector from Image multi-objective examples (see libraries/Image.ae fitness_*).
_MULTIOBJ_LABELS = ("bw_mse", "half_mse", "rows_bad", "cols_bad", "pixels_bad")


def _format_quality(quality: Any) -> str:
    """Pretty-print fitness from geneticengine (`Fitness`) or raw numeric lists."""
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


def _pretty_program(solution: Term) -> str:
    try:
        return pretty_print_sterm(lift(solution))
    except Exception:
        return str(solution)


class TerminalUI(SynthesisUI):
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
        print(
            f"# Synthesis target: ?{target_name} :: {target_type} | "
            f"budget={budget}s | each line is one evaluated candidate (pareto memory updates on `best`).",
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

    def end(self, solution: Term, quality: Any):
        pass
