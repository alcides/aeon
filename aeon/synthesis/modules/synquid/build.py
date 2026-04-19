"""Backward-compatible exports for Synquid synthesis (implementation in ``engine``)."""

from aeon.synthesis.modules.synquid.engine import (
    closing,
    frange,
    match_type,
    monomorfic,
    synthes,
    synthes_memory,
    uncurry,
)
from aeon.synthesis.modules.synquid.search import (
    iter_candidates_size_then_level,
    sorted_level_candidates,
    term_size,
)

__all__ = [
    "closing",
    "frange",
    "iter_candidates_size_then_level",
    "match_type",
    "monomorfic",
    "sorted_level_candidates",
    "synthes",
    "synthes_memory",
    "term_size",
    "uncurry",
]
