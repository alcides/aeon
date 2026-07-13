"""The ``sygus`` synthesizer backend (issue #49).

Glues the three phases together:

1. translate the hole + context to a SyGuS problem (``build_sygus_problem``),
2. solve it with the cvc5 SyGuS Python API (``solve_with_cvc5``),
3. take the reverse-translated Aeon-core term, type-check it with the
   supplied ``validate`` callback, and return it.

Outside the supported subset, when cvc5 is unavailable, or when no solution
validates, it raises ``SynthesisNotSuccessful`` cleanly.
"""

from __future__ import annotations

import time
from typing import Callable

from loguru import logger

from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer, SynthesisNotSuccessful
from aeon.synthesis.modules.sygus.solver import CVC5Unavailable, solve_with_cvc5
from aeon.synthesis.modules.sygus.translation import build_sygus_problem, problem_to_sl
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


class SygusSynthesizer(Synthesizer):
    """Synthesize base-type holes (Int/Bool/Float) by reduction to SyGuS, solved by cvc5."""

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
        start = time.time()

        problem = build_sygus_problem(ctx, type, fun_name=fun_name.name)
        if problem is None:
            raise SynthesisNotSuccessful(
                f"SygusSynthesizer: hole of type {type} is outside the SyGuS-supported subset "
                "(needs an Int/Bool/Float type, optionally refined, over native operators).",
            )

        logger.log("SYNTHESIZER", f"SyGuS problem:\n{problem_to_sl(problem)}")

        timeout_ms = max(1000, int(budget * 1000))
        try:
            candidate = solve_with_cvc5(problem, timeout_ms)
        except CVC5Unavailable as exc:
            raise SynthesisNotSuccessful(str(exc)) from exc

        if candidate is None:
            raise SynthesisNotSuccessful("SygusSynthesizer: cvc5 found no candidate within budget")

        try:
            ok = validate(candidate)
        except Exception:
            ok = False
        if not ok:
            raise SynthesisNotSuccessful(
                f"SygusSynthesizer: candidate {candidate} did not type-check against {type}",
            )

        ui.register(candidate, [], time.time() - start, True)
        return candidate
