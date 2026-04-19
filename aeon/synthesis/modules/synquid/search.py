"""Search helpers for Synquid-style synthesis (ordering, size heuristics)."""

from __future__ import annotations

import heapq
import itertools
from collections.abc import Callable, Iterator

from aeon.core.terms import Annotation, Application, Hole, If, Literal, Term, TypeApplication, Var
from aeon.core.types import Type
from aeon.synthesis.modules.synquid.engine import synthes_memory
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


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
    """Yield candidates from ``synthes_memory`` for this level, smallest ``term_size`` first."""
    batch = list(synthes_memory(ctx, level, ret_t, skip, mem))
    batch.sort(key=term_size)
    yield from batch


def iter_candidates_size_then_level(
    ctx: TypingContext,
    ret_t: Type,
    skip: Callable[[Name], bool],
    mem: dict,
    *,
    max_level: int = 128,
    seed_levels: int = 2,
) -> Iterator[Term]:
    """Merge synthesis levels lazily: smaller ``term_size`` first; tie-break shallower ``level``.

    Unlike strict iterative deepening (exhaust level *L* before *L+1*), this interleaves
    levels so a compact term at depth *L+1* can be tried before a bulky term at depth *L*.
    Deeper levels are opened when the previous frontier level is exhausted.
    """
    tie = itertools.count()
    heap: list[tuple[int, int, int, Term]] = []
    itors: dict[int, Iterator[Term]] = {}

    for L in range(min(seed_levels, max_level + 1)):
        if L not in itors:
            itors[L] = iter(sorted_level_candidates(ctx, L, ret_t, skip, mem))
        first = next(itors[L], None)
        if first is not None:
            heapq.heappush(heap, (term_size(first), L, next(tie), first))

    while heap:
        _, lv, _, t = heapq.heappop(heap)
        yield t
        nxt = next(itors[lv], None)
        if nxt is not None:
            heapq.heappush(heap, (term_size(nxt), lv, next(tie), nxt))
            continue
        probe = max(itors.keys(), default=-1) + 1
        while probe <= max_level:
            if probe not in itors:
                itors[probe] = iter(sorted_level_candidates(ctx, probe, ret_t, skip, mem))
            cand = next(itors[probe], None)
            if cand is not None:
                heapq.heappush(heap, (term_size(cand), probe, next(tie), cand))
                break
            probe += 1
