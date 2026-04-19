"""Search helpers for Synquid-style synthesis (ordering, size heuristics)."""

from __future__ import annotations

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
