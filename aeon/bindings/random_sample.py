"""Batch sampling helpers for ``libraries/Distributions.ae`` (issue #441).

All functions draw from a Python ``random.Random`` instance (the runtime
representation of aeon's linear ``Rng``) so sample batches never touch the
global ``numpy.random`` / ``random.random()`` state.
"""

from __future__ import annotations

import math
from typing import Any


def poisson_batch(lam: float, n: int, g: Any) -> list[float]:
    """Draw *n* Poisson(*lam*) samples using Knuth's algorithm on *g*."""
    out: list[float] = []
    for _ in range(n):
        threshold = math.exp(-lam)
        k = 0
        p = 1.0
        while p > threshold:
            k += 1
            p *= g.random()
        out.append(float(k - 1))
    return out
