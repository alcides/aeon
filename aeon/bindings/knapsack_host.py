"""Host-only helpers for KnapsackGA setup (not the evolutionary loop)."""

from __future__ import annotations

import random
from typing import Any


def fill_pop(buf: list[Any], n: int, seed: int) -> list[Any]:
    rng = random.Random(seed)
    for i in range(n):
        buf[i] = 1 if rng.random() < 0.15 else 0
    return buf


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
