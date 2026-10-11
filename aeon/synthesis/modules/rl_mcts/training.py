"""Build training callbacks through the normal Aeon compiler and verifier."""

from __future__ import annotations

from collections.abc import Callable
from pathlib import Path

from aeon.core.types import top
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.entrypoint import make_program, make_validator
from aeon.synthesis.identification import get_holes_info, incomplete_functions_and_holes
from aeon.synthesis.modules.rl_mcts.features import Syntax
from aeon.synthesis.modules.rl_mcts.search import DefaultGuidance, Guidance, SearchConfig, SearchResult
from aeon.synthesis.modules.rl_mcts.synthesizer import RLMCTSSynthesizer
from aeon.synthesis.modules.tdsyn.worklist import PartialAST
from aeon.synthesis.uis.api import SilentSynthesisUI


def aeon_problem(
    source: Path,
    *,
    budget: float = 10,
    seed: int = 0,
    config: SearchConfig = SearchConfig(),
) -> Callable[[Guidance | None], tuple[Syntax, SearchResult[PartialAST]]]:
    """One independent refinement hole per file; no examples/optimization goals."""
    driver = AeonDriver(AeonConfig("rl_mcts", SilentSynthesisUI(), max(1, int(budget)), no_main=True))
    errors = list(driver.parse(filename=str(source)))
    if errors:
        raise ValueError(f"cannot compile training source {source}: {errors}")
    assert driver.core is not None and driver.typing_ctx is not None
    core, ctx = driver.core, driver.typing_ctx
    with driver.session.activate():
        targets = incomplete_functions_and_holes(ctx, core)
        if len(targets) != 1 or len(targets[0][1]) != 1:
            raise ValueError("Aeon training sources must contain exactly one independent hole")
        fun_name, (hole_name,) = targets[0]
        target, hole_ctx = get_holes_info(ctx, core, top, targets, refined_types=True)[hole_name]
        if driver.metadata.get(fun_name, {}).get("goals"):
            raise ValueError("Aeon RL training requires refinement specifications, not objective decorators")

    def run(guidance: Guidance | None) -> tuple[Syntax, SearchResult[PartialAST]]:
        backend = RLMCTSSynthesizer(seed, guidance or DefaultGuidance(), config)
        with driver.session.activate():
            try:
                backend.synthesize(
                    hole_ctx,
                    target,
                    make_validator(ctx, make_program(core, hole_name)),
                    lambda _: [],
                    fun_name,
                    driver.metadata,
                    budget=budget,
                    ui=SilentSynthesisUI(),
                )
            except SynthesisNotSuccessful:
                pass  # Failed searches are zero-valued training examples.
        assert backend.last_spec is not None and backend.last_result is not None
        return backend.last_spec, backend.last_result

    return run
