"""Search helpers for Synquid-style synthesis (ordering, size heuristics)."""

from __future__ import annotations

import heapq
import itertools
from itertools import islice
from collections.abc import Callable, Iterator

from aeon.core.terms import Annotation, Application, Hole, If, Literal, Term, TypeApplication, Var
from aeon.core.types import Type
from aeon.synthesis.modules.synquid.engine import synthes_memory
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name

# When the depth is unbounded, treat this many consecutive empty deeper levels
# as exhaustion of the candidate space (so the merge ends instead of probing
# ever-deeper empty levels forever).
_EMPTY_PROBE_LIMIT = 16

# Cap on how many candidates of a single level are materialised+sorted at once,
# so opening a deep (potentially huge) level can't blow past the time budget.
_LEVEL_BATCH_CAP = 4000


def term_size(t: Term) -> int:
    """Rough AST node count for prioritising smaller candidates."""
    match t:
        case Var() | Hole() | Literal():
            return 1
        case Annotation(e, _):
            return 1 + term_size(e)
        case Application(f, a):
            return 1 + term_size(f) + term_size(a)
        case If(c, th, el):
            return 1 + term_size(c) + term_size(th) + term_size(el)
        case TypeApplication(b, _):
            return 1 + term_size(b)
        case _:
            n = 1
            for attr in ("body", "expr", "cond", "then", "otherwise", "var_value", "fun", "arg"):
                if hasattr(t, attr):
                    n += term_size(getattr(t, attr))
            return n


def sorted_level_candidates(
    ctx: TypingContext,
    level: int,
    ret_t: Type,
    skip: Callable[[Name], bool],
    mem: dict,
) -> Iterator[Term]:
    """Yield candidates from ``synthes_memory`` for this level, smallest ``term_size`` first.

    The level is materialised so it can be sorted by size, but only up to
    ``_LEVEL_BATCH_CAP`` candidates: a deep level can hold an enormous number of
    terms, and materialising all of them (with no budget check) would blow past
    the time budget. The cap keeps each level's setup bounded; the cross-level
    merge still reaches deeper levels."""
    batch = list(islice(synthes_memory(ctx, level, ret_t, skip, mem), _LEVEL_BATCH_CAP))
    batch.sort(key=term_size)
    yield from batch


def iter_candidates_size_then_level(
    ctx: TypingContext,
    ret_t: Type,
    skip: Callable[[Name], bool],
    mem: dict,
    *,
    max_level: int | None = None,
    seed_levels: int = 2,
) -> Iterator[Term]:
    """Merge synthesis levels lazily: smaller ``term_size`` first; tie-break shallower ``level``.

    Unlike strict iterative deepening (exhaust level *L* before *L+1*), this interleaves
    levels so a compact term at depth *L+1* can be tried before a bulky term at depth *L*.
    Deeper levels are opened when the previous frontier level is exhausted.

    ``max_level`` defaults to ``None`` (unbounded): the search keeps deepening until
    the caller's time budget stops consuming candidates, or the space is exhausted
    (``_EMPTY_PROBE_LIMIT`` consecutive empty deeper levels). A concrete
    ``max_level`` caps the depth explicitly.
    """
    tie = itertools.count()
    heap: list[tuple[int, int, int, Term]] = []
    itors: dict[int, Iterator[Term]] = {}

    def push_from(level: int) -> bool:
        """Open ``level`` (if needed) and push its next candidate; True if one was pushed."""
        if level not in itors:
            itors[level] = iter(sorted_level_candidates(ctx, level, ret_t, skip, mem))
        cand = next(itors[level], None)
        if cand is not None:
            heapq.heappush(heap, (term_size(cand), level, next(tie), cand))
            return True
        return False

    def open_deeper() -> None:
        """Open the shallowest not-yet-opened level that yields a candidate, so the
        merge keeps deepening. Bounded: stop at ``max_level``, or after a run of
        empty levels (the space is exhausted -- never spin forever)."""
        probe = max(itors.keys(), default=-1) + 1
        empties = 0
        while True:
            if max_level is not None and probe > max_level:
                return
            if max_level is None and empties >= _EMPTY_PROBE_LIMIT:
                return
            if push_from(probe):
                return
            probe += 1
            empties += 1

    seed = seed_levels if max_level is None else min(seed_levels, max_level + 1)
    for L in range(seed):
        push_from(L)
    # A goal whose constructor needs arguments has *no* candidates at the shallow
    # seed levels (e.g. `Level`, only buildable at depth >= 2). Bootstrap by
    # opening deeper levels until candidates appear, instead of returning empty.
    if not heap:
        open_deeper()

    while heap:
        _, lv, _, t = heapq.heappop(heap)
        yield t
        nxt = next(itors[lv], None)
        if nxt is not None:
            heapq.heappush(heap, (term_size(nxt), lv, next(tie), nxt))
            continue
        open_deeper()
