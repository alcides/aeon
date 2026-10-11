"""Aeon adapter for the Parsert/Polgreen RL-guided grammar-tree search."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import replace
import os
from time import monotonic

from aeon.core.terms import Term
from aeon.core.types import Type, refined_to_unrefined_type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer, SynthesisNotSuccessful
from aeon.synthesis.modules.native_search import expansions_for_hole, initial_partial, make_skip
from aeon.synthesis.modules.rl_mcts.features import Syntax, syntax
from aeon.synthesis.modules.rl_mcts.learning import LearnedGuidance
from aeon.synthesis.modules.rl_mcts.search import Guidance, SearchConfig, SearchResult, search
from aeon.synthesis.modules.tdsyn.helpers import clear_tdsyn_caches
from aeon.synthesis.modules.tdsyn.worklist import PartialAST, locate_holes
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def grammar_successors(
    partial: PartialAST,
    skip: Callable[[Name], bool],
    max_depth: int,
    describe: Callable[[PartialAST], Syntax],
) -> list[PartialAST]:
    # Erasure is local to proposal generation; the acceptance oracle is intact.
    hole = replace(partial.holes[0], expected_type=refined_to_unrefined_type(partial.holes[0].expected_type))
    options = expansions_for_hole(partial, hole, skip, max_depth)
    unique: dict[Syntax, PartialAST] = {}
    for option in options:
        # Shared expansion appends new subgoals after existing sibling holes.
        # The paper requires textual leftmost expansion, not that queue order.
        order = {name: index for index, name in enumerate(locate_holes(option.term))}
        option = replace(option, holes=sorted(option.holes, key=lambda h: order[h.name]))
        unique.setdefault(describe(option), option)
    return list(unique.values())


class RLMCTSSynthesizer(Synthesizer):
    def __init__(
        self, seed: int = 0, guidance: Guidance | None = None, config: SearchConfig = SearchConfig(), max_depth: int = 8
    ):
        if max_depth < 0:
            raise ValueError("max_depth must be nonnegative")
        self.seed = seed
        self.guidance = guidance
        self.config = config
        self.max_depth = max_depth
        self.last_result: SearchResult[PartialAST] | None = None
        self.last_spec: Syntax | None = None

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
        self.last_result = None
        self.last_spec = None
        # The paper is a satisfiability solver, not a numerical optimizer.
        # Reject goals explicitly instead of returning an arbitrary "optimum".
        if metadata.get(fun_name, {}).get("goals"):
            raise SynthesisNotSuccessful(
                "rl_mcts solves refinement specifications; optimization goals are not supported"
            )
        clear_tdsyn_caches()
        names: dict[Name, str] = {}
        self.last_spec = syntax((type, ctx.vars()), names)
        skip = make_skip(fun_name, metadata)
        started = monotonic()
        assessed = 0

        def describe(partial: PartialAST) -> Syntax:
            return syntax(partial.term, dict(names))

        def expand(partial: PartialAST) -> list[PartialAST]:
            # Grammar admissibility is structural. Applying a function does not
            # have to prove the final refinement until its arguments are known.
            # Erasure is local to proposal generation; validate is untouched.
            return grammar_successors(partial, skip, self.max_depth, describe)

        def verify(partial: PartialAST) -> bool:
            nonlocal assessed
            assessed += 1
            valid = validate(partial.term)
            elapsed = monotonic() - started
            ui.register(partial.term, [] if valid else "Invalid", elapsed, valid)
            ui.progress(assessed, assessed, elapsed)
            return valid

        guidance = self.guidance
        model_path = os.environ.get("AEON_RL_MCTS_MODEL")
        if guidance is None and model_path:
            guidance = LearnedGuidance.load(model_path)
        self.last_result = search(
            initial_partial(ctx, type),
            self.last_spec,
            describe,
            lambda p: len(p.holes),
            expand,
            verify,
            guidance=guidance,
            config=self.config,
            budget=budget,
            seed=self.seed,
        )
        if self.last_result.solution is not None:
            return self.last_result.solution.state.term
        raise SynthesisNotSuccessful(f"rl_mcts: {self.last_result.reason}; {assessed} complete candidates checked")
