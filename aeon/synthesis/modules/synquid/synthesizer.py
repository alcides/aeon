"""Synquid-style synthesizer: search over ``engine`` (Q-aware guards, spine prune).

Default order is ``size_merge`` (heap by AST size, then level); optional ``iterative_deepening``.
"""

from time import monotonic_ns
from typing import Any, Callable

from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer, SynthesisNotSuccessful
from aeon.synthesis.grammar.utils import SYNTHESIS_EXCLUDED_NAMES
from aeon.synthesis.modules.synquid.search import iter_candidates_size_then_level, sorted_level_candidates
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name


def _dominates(a: list[float], b: list[float]) -> bool:
    return all(x <= y for x, y in zip(a, b)) and any(x < y for x, y in zip(a, b))


def _update_pareto_front(
    front: list[tuple[list[float], Any]],
    score: list[float],
    result: Any,
) -> list[tuple[list[float], Any]]:
    if any(_dominates(existing_score, score) for existing_score, _ in front):
        return front
    return [(s, r) for s, r in front if not _dominates(score, s)] + [(score, result)]


def _pick_pareto_member(front: list[tuple[list[float], Any]]) -> Any:
    _, result = min(front, key=lambda item: (sum(item[0]), item[0]))
    return result


def get_elapsed_time(start_time) -> float:
    """The elapsed time since the start in seconds."""
    return (monotonic_ns() - start_time) * 0.000000001


class SynquidSynthesizer(Synthesizer):
    def synthesize(
        self,
        ctx: TypingContext,
        type: Type,
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        fun_name: Name,
        metadata: Metadata,
        budget: float = 60,
        ui: SynthesisUI = SynthesisUI(),
        output_value: Callable[[Term], object] | None = None,
    ) -> Term:
        assert isinstance(ctx, TypingContext)
        assert isinstance(type, Type)

        current_metadata = metadata.get(fun_name, {})
        is_recursion_allowed = current_metadata.get("recursion", False)

        def skip(name: Name) -> bool:
            if name == fun_name:
                return not is_recursion_allowed
            elif name.name in SYNTHESIS_EXCLUDED_NAMES:
                return True
            else:
                return False

        start_time = monotonic_ns()
        done = True
        level = 0
        pareto_front: list[tuple[list[float], Any]] = []
        mem: dict = {}
        ui.register(None, None, 0, True)
        goals = current_metadata.get("goals", [])
        search_mode = current_metadata.get("synquid_search", "size_merge")
        typecheck_candidate_first = bool(current_metadata.get("synquid_typecheck_candidate_first", False))
        # Depth is unbounded by default: the search runs until the time budget
        # (the budget check in `consider`) or the candidate space is exhausted.
        # A concrete `synquid_max_level` caps the depth explicitly.
        _max_level_raw = current_metadata.get("synquid_max_level")
        max_level = None if _max_level_raw is None else max(0, int(_max_level_raw))
        seed_levels = max(1, int(current_metadata.get("synquid_seed_levels", 2)))
        max_candidates_raw = current_metadata.get("synquid_max_candidates")
        max_candidates = None if max_candidates_raw is None else max(0, int(max_candidates_raw))
        n_candidates = 0

        def _safe_check(fn, *args) -> bool:
            # A candidate that makes the typechecker/SMT raise (e.g. an
            # ill-sorted intermediate term) is simply rejected, never fatal.
            try:
                return bool(fn(*args))
            except Exception:
                return False

        def finish() -> Term:
            if not pareto_front:
                raise SynthesisNotSuccessful("SynquidSynthesizer: no valid candidate found within budget")
            return _pick_pareto_member(pareto_front)

        def consider(result: Term) -> bool:
            nonlocal pareto_front, done
            if typecheck_candidate_first and not _safe_check(check_type, ctx, result, type):
                ui.register(result, "Invalid (hole-local)", get_elapsed_time(start_time), False)
                if get_elapsed_time(start_time) > budget:
                    done = False
                return False
            if _safe_check(validate, result):
                score = evaluate(result)
                if not goals:
                    ui.register(result, score, get_elapsed_time(start_time), True)
                    return True
                pareto_front = _update_pareto_front(pareto_front, score, result)
                on_front = any(r is result for _, r in pareto_front)
                ui.register(result, score, get_elapsed_time(start_time), on_front)
                if all(s == 0.0 for s in score):
                    return True
            else:
                ui.register(result, "Invalid", get_elapsed_time(start_time), False)
            if get_elapsed_time(start_time) > budget:
                done = False
            return False

        if search_mode == "iterative_deepening":
            while done and (max_level is None or level <= max_level):
                cap_done = False
                for result in sorted_level_candidates(ctx, level, type, skip, mem):
                    if max_candidates is not None and n_candidates >= max_candidates:
                        cap_done = True
                        done = False
                        break
                    n_candidates += 1
                    if consider(result):
                        return result
                    if not done:
                        break
                if cap_done:
                    break
                level += 1
            return finish()

        for result in iter_candidates_size_then_level(
            ctx, type, skip, mem, max_level=max_level, seed_levels=seed_levels
        ):
            if max_candidates is not None and n_candidates >= max_candidates:
                break
            n_candidates += 1
            if consider(result):
                return result
            if not done:
                break
        return finish()
