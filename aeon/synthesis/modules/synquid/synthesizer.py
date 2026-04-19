"""Synquid-style synthesizer: search over ``engine`` (Q-aware guards, spine prune).

Default order is ``size_merge`` (heap by AST size, then level); optional ``iterative_deepening``.
"""

from time import monotonic_ns
from typing import Any, Callable

from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer
from aeon.synthesis.modules.synquid.search import iter_candidates_size_then_level, sorted_level_candidates
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name


def is_better(v1, v2):
    if not v2:
        return True
    return all(x < y for x, y in zip(v1, v2))


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
    ) -> Term:
        assert isinstance(ctx, TypingContext)
        assert isinstance(type, Type)

        current_metadata = metadata.get(fun_name, {})
        is_recursion_allowed = current_metadata.get("recursion", False)
        vars_to_ignore = current_metadata.get("hide", [])

        def skip(name: Name) -> bool:
            if name == fun_name:
                return not is_recursion_allowed
            elif name in vars_to_ignore:
                return True
            elif name.name.startswith("__internal__"):
                return True
            elif name.name in ["native", "native_import", "print"]:
                return True
            else:
                return False

        start_time = monotonic_ns()
        done = True
        level = 0
        best: tuple[list[float], Any] = ([], None)
        mem: dict = {}
        ui.register(None, None, 0, True)
        goals = current_metadata.get("goals", [])
        search_mode = current_metadata.get("synquid_search", "size_merge")
        typecheck_candidate_first = bool(current_metadata.get("synquid_typecheck_candidate_first", False))
        max_level = max(0, int(current_metadata.get("synquid_max_level", 128)))
        seed_levels = max(1, int(current_metadata.get("synquid_seed_levels", 2)))
        max_candidates_raw = current_metadata.get("synquid_max_candidates")
        max_candidates = None if max_candidates_raw is None else max(0, int(max_candidates_raw))
        n_candidates = 0

        def consider(result: Term) -> bool:
            nonlocal best, done
            if typecheck_candidate_first and not check_type(ctx, result, type):
                ui.register(result, "Invalid (hole-local)", get_elapsed_time(start_time), False)
                if get_elapsed_time(start_time) > budget:
                    done = False
                return False
            if validate(result):
                score = evaluate(result)
                if not goals:
                    ui.register(result, score, get_elapsed_time(start_time), True)
                    return True
                if is_better(score, best[0]):
                    best = (score, result)
                    ui.register(result, score, get_elapsed_time(start_time), True)
                else:
                    ui.register(result, score, get_elapsed_time(start_time), False)
            else:
                ui.register(result, "Invalid", get_elapsed_time(start_time), False)
            if get_elapsed_time(start_time) > budget:
                done = False
            return False

        if search_mode == "iterative_deepening":
            while done and level <= max_level:
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
            return best[1]

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
        return best[1]
