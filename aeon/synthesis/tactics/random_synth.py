from __future__ import annotations

import random
import time
from typing import Callable

from aeon.core.terms import Hole, Term
from aeon.core.types import Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer, SynthesisNotSuccessful
from aeon.synthesis.pareto import ParetoEntry, minimize_flags_from_goals, pick_pareto_member, update_pareto_front
from aeon.synthesis.tactics.assumption import tactic_assumption
from aeon.synthesis.tactics.builtin import tactic_apply_question, tactic_constructor
from aeon.synthesis.tactics.by_cases import tactic_by_cases
from aeon.synthesis.tactics.choose_literal import tactic_choose_literal
from aeon.synthesis.tactics.inst import tactic_inst
from aeon.synthesis.tactics.split import tactic_split
from aeon.synthesis.tactics.holes import collect_hole_judgments
from aeon.synthesis.tactics.state import TacticState
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name, fresh_counter

_loc = SynthesizedLocation("tactics")


class TacticRandomSynthesizer(Synthesizer):
    """Random tactic search: ``apply?``, ``assumption``, ``constructor``, ``inst``, ``choose_literal``, ``by_cases``, ``split``."""

    def __init__(self, seed: int = 0):
        self.seed = seed

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
        goals = current_metadata.get("goals", [])
        has_goals = bool(goals)
        minimize = minimize_flags_from_goals(goals)
        rng = random.Random(self.seed)
        tactics = [
            tactic_apply_question,
            tactic_assumption,
            tactic_constructor,
            tactic_inst,
            tactic_choose_literal,
            tactic_by_cases,
            tactic_split,
        ]

        start = time.time()
        deadline = start + float(budget)
        front: list[ParetoEntry] = []
        max_tactic_steps = 20

        while time.time() < deadline:
            # Start a fresh random tactic walk each iteration
            root = Name("_root", fresh_counter.fresh())
            state = TacticState(ctx, Hole(root, loc=_loc), type)

            steps = 0
            stuck = False
            while time.time() < deadline and steps < max_tactic_steps:
                holes = collect_hole_judgments(state.ctx, state.term, state.goal, refined_types=True)
                if not holes:
                    break  # complete — evaluate below
                focal = rng.choice(list(holes.keys()))
                tact = rng.choice(tactics)
                nxt = tact(state, focal)
                if nxt is not None:
                    state = nxt
                    steps += 1
                else:
                    # Tactic failed on this hole — try a few more random tactics
                    retries = 3
                    applied = False
                    for _ in range(retries):
                        alt_tact = rng.choice(tactics)
                        alt_nxt = alt_tact(state, focal)
                        if alt_nxt is not None:
                            state = alt_nxt
                            steps += 1
                            applied = True
                            break
                    if not applied:
                        stuck = True
                        break

            if stuck:
                continue

            # Check if complete (no remaining holes)
            holes = collect_hole_judgments(state.ctx, state.term, state.goal, refined_types=True)
            if holes:
                continue

            elapsed = time.time() - start
            try:
                if not validate(state.term):
                    ui.register(state.term, "Invalid", elapsed, False)
                    continue
            except Exception:
                ui.register(state.term, "Invalid", elapsed, False)
                continue

            # No optimization goals — return immediately
            if not has_goals:
                ui.register(state.term, [], elapsed, True)
                return state.term

            try:
                score = evaluate(state.term)
            except Exception:
                ui.register(state.term, "Invalid", elapsed, False)
                continue

            front, is_best = update_pareto_front(front, score, state.term, minimize)
            ui.register(state.term, score, elapsed, is_best)

        if front:
            return pick_pareto_member(front, self.seed)
        raise SynthesisNotSuccessful("TacticRandomSynthesizer: no valid candidate found within budget")
