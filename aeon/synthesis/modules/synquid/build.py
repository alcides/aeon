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

__all__ = [
    "closing",
    "frange",
    "match_type",
    "monomorfic",
    "synthes",
    "synthes_memory",
    "uncurry",
]
