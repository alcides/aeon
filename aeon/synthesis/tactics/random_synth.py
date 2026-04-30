from __future__ import annotations

import random
import time
from typing import Callable

from aeon.core.terms import Hole, Term
from aeon.core.types import Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer, SynthesisNotSuccessful
from aeon.synthesis.tactics.assumption import tactic_assumption
from aeon.synthesis.tactics.builtin import tactic_apply_question, tactic_constructor
from aeon.synthesis.tactics.by_cases import tactic_by_cases
from aeon.synthesis.tactics.choose_literal import tactic_choose_literal
from aeon.synthesis.tactics.inst import tactic_inst
from aeon.synthesis.tactics.split import tactic_split
from aeon.synthesis.tactics.holes import collect_hole_judgments
from aeon.synthesis.tactics.state import TacticState
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext, VariableBinder
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name, fresh_counter

_loc = SynthesizedLocation("tactics")


def _is_better(v1: list[float], v2: list[float]) -> bool:
    if not v2:
        return True
    return all(x < y for x, y in zip(v1, v2))


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
    ) -> Term:
        assert isinstance(ctx, TypingContext)
        assert isinstance(type, Type)

        current_metadata = metadata.get(fun_name, {})
        hidden_names = {v.name for v in current_metadata.get("hide", [])}
        if hidden_names:
            filtered_entries = [e for e in ctx.entries if not (isinstance(e, VariableBinder) and e.name.name in hidden_names)]
            ctx = TypingContext(filtered_entries)

        has_goals = bool(current_metadata.get("goals"))
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
        best_score: list[float] = []
        best_term: Term | None = None
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

            is_best = not best_score or _is_better(score, best_score)
            if is_best:
                best_score = score
                best_term = state.term
            ui.register(state.term, score, elapsed, is_best)

        if best_term is not None:
            return best_term
        raise SynthesisNotSuccessful("TacticRandomSynthesizer: no valid candidate found within budget")
