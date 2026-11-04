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
from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.solver_problem import ConstraintSynthesizer
from aeon.synthesis.candidate_archive import CandidateArchive
from aeon.synthesis.modules.sygus.solver import CVC5Unavailable, enumerate_cvc5
from aeon.synthesis.modules.sygus.translation import build_sygus_problem, problem_to_sl
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


class SygusSynthesizer(ConstraintSynthesizer):
    """Synthesize base-type holes (Int/Bool/Float) by reduction to SyGuS, solved by cvc5."""

    supports_optimization = False
    supports_candidate_enumeration = True

    def synthesize_joint(self, holes, validate, evaluate, fun_name, metadata, budget=60, ui=SynthesisUI()):
        archive = CandidateArchive(self, fun_name, metadata, evaluate, budget, ui)
        candidates = enumerate_cvc5(metadata[fun_name]["solver_problem"], max(1, int(budget * 1000)), joint=True)
        candidate = archive.search(candidates, validate)
        if candidate is None:
            raise SynthesisNotSuccessful("Joint CVC5: no validated assignment within budget")
        return candidate

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
        archive = CandidateArchive(self, fun_name, metadata, evaluate, budget, ui)

        problem = build_sygus_problem(ctx, type, fun_name=fun_name.name)
        if problem is None:
            raise SynthesisNotSuccessful(
                f"SygusSynthesizer: hole of type {type} is outside the SyGuS-supported subset "
                "(needs an Int/Bool/Float type, optionally refined, over native operators).",
            )

        logger.log("SYNTHESIZER", f"SyGuS problem:\n{problem_to_sl(problem)}")

        timeout_ms = max(1, int((archive.deadline - time.monotonic()) * 1000))
        try:
            candidate = archive.search(enumerate_cvc5(problem, timeout_ms), validate)
        except CVC5Unavailable as exc:
            raise SynthesisNotSuccessful(str(exc)) from exc
        if candidate is None:
            raise SynthesisNotSuccessful("SygusSynthesizer: no validated candidate within budget")
        return candidate
