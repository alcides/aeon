from __future__ import annotations

import time
from collections.abc import Callable
from typing import Dict

from aeon.core.terms import Hole, Term
from aeon.core.types import Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer
from aeon.synthesis.tactics.assumption import tactic_assumption
from aeon.synthesis.tactics.builtin import tactic_apply_question, tactic_constructor
from aeon.synthesis.tactics.by_cases import tactic_by_cases
from aeon.synthesis.tactics.choose_literal import tactic_choose_literal
from aeon.synthesis.tactics.holes import collect_hole_judgments
from aeon.synthesis.tactics.inst import tactic_inst
from aeon.synthesis.tactics.split import tactic_split
from aeon.synthesis.tactics.state import TacticState
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext, VariableBinder
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name, fresh_counter

_loc = SynthesizedLocation("explicit_tactics")

TacticFn = Callable[[TacticState, Name], TacticState | None]

TACTIC_REGISTRY: Dict[str, TacticFn] = {
    "apply?": tactic_apply_question,
    "assumption": tactic_assumption,
    "constructor": tactic_constructor,
    "inst": tactic_inst,
    "choose_literal": tactic_choose_literal,
    "by_cases": tactic_by_cases,
    "split": tactic_split,
}


class ExplicitTacticSynthesizer(Synthesizer):
    """Run a fixed tactic script (surface ``by T`` or ``by (T; U; ...)``), leftmost hole each step."""

    def __init__(self, steps: tuple[str, ...]):
        self.steps = steps

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

        current_metadata = metadata.get(fun_name, {})
        hidden_names = {v.name for v in current_metadata.get("hide", [])}
        if hidden_names:
            filtered_entries = [
                e for e in ctx.entries if not (isinstance(e, VariableBinder) and e.name.name in hidden_names)
            ]
            ctx = TypingContext(filtered_entries)

        for s in self.steps:
            if s not in TACTIC_REGISTRY:
                ui.register(None, None, 0.0, False)
                return None

        root = Name("_root", fresh_counter.fresh())
        term = Hole(root, loc=_loc)
        state = TacticState(ctx, term, type)
        start = time.time()
        ui.register(None, None, 0.0, True)

        for step_name in self.steps:
            holes = collect_hole_judgments(state.ctx, state.term, state.goal, refined_types=True)
            if not holes:
                break
            focal = min(holes.keys(), key=lambda n: (n.name, n.id))
            tact = TACTIC_REGISTRY[step_name]
            nxt = tact(state, focal)
            if nxt is None:
                ui.register(state.term, None, time.time() - start, False)
                return None
            state = nxt

        holes = collect_hole_judgments(state.ctx, state.term, state.goal, refined_types=True)
        if holes:
            ui.register(state.term, None, time.time() - start, False)
            return None

        if not validate(state.term):
            ui.register(state.term, None, time.time() - start, False)
            return None

        elapsed = time.time() - start
        try:
            score = evaluate(state.term)
            ui.register(state.term, score, elapsed, True)
        except Exception:
            ui.register(state.term, "Invalid", elapsed, False)
        return state.term
