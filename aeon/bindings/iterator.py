"""Runtime helpers for ``libraries/Iterator.ae``."""

from __future__ import annotations


def from_array(arr):
    # phase 0, remaining = len(arr); store elements as a list cursor.
    return {"phase": 0, "items": list(arr), "index": 0}


def has_next(it):
    remaining = len(it["items"]) - it["index"]
    if remaining > 0:
        it = {**it, "phase": 1}
        return (True, it)
    it = {**it, "phase": 2}
    return (False, it)


def next_step(it):
    idx = it["index"]
    value = it["items"][idx]
    return (value, {**it, "phase": 0, "index": idx + 1})
