from __future__ import annotations

import random
import time
from typing import Callable

from aeon.core.terms import Hole, Term
from aeon.core.types import Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer
from aeon.synthesis.tactics.assumption import tactic_assumption
from aeon.synthesis.tactics.builtin import tactic_apply_question, tactic_constructor
from aeon.synthesis.tactics.by_cases import tactic_by_cases
from aeon.synthesis.tactics.choose_literal import tactic_choose_literal
from aeon.synthesis.tactics.split import tactic_split
from aeon.synthesis.tactics.holes import collect_hole_judgments
from aeon.synthesis.tactics.state import TacticState
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name, fresh_counter

_loc = SynthesizedLocation("tactics")


class TacticRandomSynthesizer(Synthesizer):
    """Random tactic search: ``apply?``, ``assumption``, ``constructor``, ``choose_literal``, ``by_cases``, ``split``."""

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
    ) -> Term | None:
        assert isinstance(ctx, TypingContext)
        assert isinstance(type, Type)

        rng = random.Random(self.seed)
        root = Name("_root", fresh_counter.fresh())
        term = Hole(root, loc=_loc)
        state = TacticState(ctx, term, type)
        tactics = [
            tactic_apply_question,
            tactic_assumption,
            tactic_constructor,
            tactic_choose_literal,
            tactic_by_cases,
            tactic_split,
        ]

        start = time.time()
        ui.register(None, None, 0.0, True)

        deadline = start + float(budget)
        while time.time() < deadline:
            holes = collect_hole_judgments(state.ctx, state.term, state.goal, refined_types=True)
            if not holes:
                if validate(state.term):
                    elapsed = time.time() - start
                    try:
                        score = evaluate(state.term)
                        ui.register(state.term, score, elapsed, True)
                    except Exception:
                        ui.register(state.term, "Invalid", elapsed, False)
                    return state.term
                ui.register(state.term, "Invalid", time.time() - start, False)
                return None

            focal = rng.choice(list(holes.keys()))
            tact = rng.choice(tactics)
            nxt = tact(state, focal)
            if nxt is not None:
                state = nxt

        ui.register(state.term, None, time.time() - start, False)
        return None
