"""Host-only helpers for knapsack example setup (weights/values, not the GA loop)."""

from __future__ import annotations

import random
from typing import Any


def fill_weights(buf: list[Any], n: int, seed: int) -> list[Any]:
    rng = random.Random(seed)
    for i in range(n):
        buf[i] = rng.randint(1, 50)
    return buf


def fill_values(buf: list[Any], n: int, seed: int) -> list[Any]:
    rng = random.Random(seed)
    for i in range(n):
        buf[i] = rng.randint(1, 100)
    return buf


def sum_buf(buf: list[Any], n: int) -> int:
    return int(sum(buf[:n]))
