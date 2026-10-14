"""Resumable candidate streams for synthesis-backed property inputs."""

from collections.abc import Callable, Iterator

from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.decorators.api import Metadata
from aeon.synthesis.modules.enumerative import iter_candidates
from aeon.synthesis.modules.native_search import initial_partial
from aeon.synthesis.modules.tdsyn.synthesizer import ONE_STEP_ACTIONS, TDSynSynthesizer
from aeon.synthesis.modules.tdsyn.worklist import PartialAST, expand_at_hole, fresh_hole
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name

INPUT_SYNTHESIZERS = (
    "random_search",
    "enumerative",
    "tdsyn",
    "tdsyn_enumerative",
    "tdsyn_random",
    "tdsyn_backward",
    *(name for name in ONE_STEP_ACTIONS if name != "backward"),
)


def input_candidates(
    backend: str,
    ctx: TypingContext,
    target: Type,
    fun_name: Name,
    metadata: Metadata,
    skip: Callable[[Name], bool],
    seed: int,
    max_depth: int,
) -> Iterator[Term | None]:
    """Construct a bounded stream without restarting search for each input.

    Directional, one-step variants initiate their named action, then use TDSyn
    to finish any resulting subgoals. Partial expressions are never inputs.
    ``random_search`` is handled by TypeSampler's existing bounded walks.
    """
    if backend == "enumerative":
        yield from iter_candidates(
            ctx,
            target,
            fun_name,
            metadata,
            max_depth,
            skip=skip,
            max_expansions=4096,
            max_worklist=4096,
        )
        return
    if backend in ("tdsyn", "tdsyn_enumerative", "tdsyn_random"):
        mode = "random" if backend == "tdsyn_random" else "enumerative"
        yield from TDSynSynthesizer(mode, seed).iter_input_candidates(ctx, target, skip, max_depth)
        return

    action = "backward" if backend == "tdsyn_backward" else backend
    if action not in ONE_STEP_ACTIONS:
        raise ValueError(f"Unsupported PBT input synthesizer: {backend}")
    if action == "backward_abs":
        term, hole = fresh_hole(target, ctx)
        initial = PartialAST(term, [hole], 0)
    else:
        initial = initial_partial(ctx, target)
        hole = initial.holes[0]
    search = TDSynSynthesizer("enumerative", seed)
    for replacement, holes in ONE_STEP_ACTIONS[action](hole, skip):
        partial = expand_at_hole(initial, hole, replacement, holes, 1 if holes else 0)
        yield from search.iter_input_candidates(ctx, target, skip, max_depth, initial=partial)
