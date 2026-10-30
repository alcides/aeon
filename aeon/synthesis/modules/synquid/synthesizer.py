"""Synquid-style synthesizer: round-trip constraints and branch-first abduction.

Default order follows §3.7 at increasing application depth; legacy size ordering is optional.
"""

from time import monotonic_ns, monotonic
from typing import Callable

from aeon.core.terms import Term
from aeon.core.types import Type, TypePolymorphism, AbstractionType
from aeon.decorators.api import Metadata
from aeon.synthesis.api import (
    Synthesizer,
    SynthesisNotSuccessful,
    InvalidIndividualException,
    TimeoutInEvaluationException,
)
from aeon.synthesis.grammar.utils import SYNTHESIS_EXCLUDED_NAMES
from aeon.synthesis.modules.synquid.solver import SearchStats
from aeon.synthesis.modules.synquid.search import iter_candidates_size_then_level, sorted_level_candidates
from aeon.synthesis.pareto import ParetoEntry, minimize_flags_from_goals, pick_pareto_member, update_pareto_front
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name


def get_elapsed_time(start_time) -> float:
    """The elapsed time since the start in seconds."""
    return (monotonic_ns() - start_time) * 0.000000001


class SynquidSynthesizer(Synthesizer):
    def __init__(self, seed: int = 0):
        self.seed = seed
        self.stats = SearchStats()

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
        pareto_front: list[ParetoEntry] = []
        self.stats = SearchStats()
        mem: dict = {
            "synquid_stats": self.stats,
            "synquid_deadline": monotonic() + budget,
            "synquid_match_depth": current_metadata.get("synquid_match_depth", 2),
        }
        ui.register(None, None, 0, True)
        goals = current_metadata.get("goals", [])
        minimize = minimize_flags_from_goals(goals)
        search_mode = current_metadata.get("synquid_search", "paper")
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
        search_type = type

        def close_candidate(term):
            return term

        # Surface declarations already contain TABS/ABS around a scalar hole.
        # Reconstruct the complete schema for FIX, then apply the verified local
        # function to those existing parameters. The outer program is untouched.
        if not is_recursion_allowed and not isinstance(type, (TypePolymorphism, AbstractionType)):
            from aeon.synthesis.modules.synquid.functions import enclosing_function

            prepared = enclosing_function(ctx, fun_name, type)
            if prepared is not None:
                search_type, close_candidate = prepared

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
            ui.register_front(pareto_front, get_elapsed_time(start_time))
            return pick_pareto_member(pareto_front, self.seed)

        def consider(result: Term) -> bool:
            nonlocal pareto_front, done
            result = close_candidate(result)
            if typecheck_candidate_first and not _safe_check(check_type, ctx, result, type):
                ui.register(result, "Invalid (hole-local)", get_elapsed_time(start_time), False)
                if get_elapsed_time(start_time) > budget:
                    done = False
                return False
            self.stats.full_validations += 1
            if _safe_check(validate, result):
                if not goals:
                    ui.register(result, [], get_elapsed_time(start_time), True)
                    return True
                try:
                    score = evaluate(result)
                except (InvalidIndividualException, TimeoutInEvaluationException):
                    ui.register(result, "Invalid (evaluation)", get_elapsed_time(start_time), False)
                    if get_elapsed_time(start_time) > budget:
                        done = False
                    return False
                pareto_front, on_front = update_pareto_front(pareto_front, score, result, minimize)
                elapsed = get_elapsed_time(start_time)
                if on_front:
                    ui.register_front(pareto_front, elapsed)
                ui.register(result, score, elapsed, on_front)
                if all(s == 0.0 for s in score):
                    return True
            else:
                ui.register(result, "Invalid", get_elapsed_time(start_time), False)
            if get_elapsed_time(start_time) > budget:
                done = False
            return False

        if search_mode == "paper":
            from itertools import islice
            from aeon.synthesis.modules.synquid.engine import synthes_memory
            from aeon.synthesis.modules.synquid.search import _LEVEL_BATCH_CAP

            while monotonic() < mem["synquid_deadline"] and (max_level is None or level <= max_level):
                for result in islice(synthes_memory(ctx, level, search_type, skip, mem), _LEVEL_BATCH_CAP):
                    if max_candidates is not None and n_candidates >= max_candidates:
                        return finish()
                    n_candidates += 1
                    if consider(result):
                        return close_candidate(result)
                level += 1
            return finish()

        if search_mode == "iterative_deepening":
            while done and (max_level is None or level <= max_level):
                cap_done = False
                for result in sorted_level_candidates(ctx, level, search_type, skip, mem):
                    if max_candidates is not None and n_candidates >= max_candidates:
                        cap_done = True
                        done = False
                        break
                    n_candidates += 1
                    if consider(result):
                        return close_candidate(result)
                    if not done:
                        break
                if cap_done:
                    break
                level += 1
            return finish()

        for result in iter_candidates_size_then_level(
            ctx, search_type, skip, mem, max_level=max_level, seed_levels=seed_levels
        ):
            if max_candidates is not None and n_candidates >= max_candidates:
                break
            n_candidates += 1
            if consider(result):
                return close_candidate(result)
            if not done:
                break
        return finish()
