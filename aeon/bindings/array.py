"""NumPy-backed implementations of the numeric ``Array`` operations.

The polymorphic, structural part of the ``Array`` library (``new``, ``append``,
``cons``, ``get``, ``map``, ...) stays plain-Python-list backed -- that is what
the rest of the ecosystem (String, Json, Args, the 99-problems / PSB2 examples)
relies on, and prepend/index are O(n) either way. The *numeric* operations,
however, are the ones that benefit from vectorisation, so they are computed with
NumPy here.

Every function accepts an ordinary Python list (or anything ``np.asarray`` can
ingest) and returns a *native* Python value -- ``list`` via ``.tolist()`` or a
Python ``int``/``float`` -- never a bare NumPy array or scalar. That keeps the
``Array`` runtime representation a uniform Python list (so structural ops keep
working on results) and stops NumPy scalar types (``np.int64``/``np.bool_``)
from leaking into Aeon's ``Int``/``Bool`` (which the ``--test`` runner rejects).
"""

from __future__ import annotations

import numpy as np

from aeon.bindings.binding_utils import curried


def _ints(a) -> np.ndarray:
    return np.asarray(a, dtype=np.int64)


# ── Reductions (Array Int -> scalar) ────────────────────────────────────────


@curried
def Array_sum(a):
    return int(_ints(a).sum())


@curried
def Array_dot(a, b):
    return int(np.dot(_ints(a), _ints(b)))


@curried
def Array_mean(a):
    return float(_ints(a).mean())


@curried
def Array_max_element(a):
    return int(_ints(a).max())


@curried
def Array_min_element(a):
    return int(_ints(a).min())


@curried
def Array_argmax(a):
    return int(_ints(a).argmax())


@curried
def Array_argmin(a):
    return int(_ints(a).argmin())


# ── Counting (Array Int -> bounded Int) ─────────────────────────────────────


@curried
def Array_count_ge(a, t):
    return int((_ints(a) >= t).sum())


@curried
def Array_count_le(a, t):
    return int((_ints(a) <= t).sum())


@curried
def Array_count_eq(a, v):
    return int((_ints(a) == v).sum())


# ── Builders (-> Array Int) ─────────────────────────────────────────────────


@curried
def Array_zeros(n):
    return np.zeros(int(n), dtype=np.int64).tolist()


@curried
def Array_replicate(n, x):
    return np.full(int(n), x, dtype=np.int64).tolist()


# ── Element-wise maps (Array Int -> Array Int, length preserved) ────────────


@curried
def Array_scale(a, k):
    return (_ints(a) * k).tolist()


@curried
def Array_offset(a, k):
    return (_ints(a) + k).tolist()


@curried
def Array_clamp(a, lo, hi):
    return np.clip(_ints(a), lo, hi).tolist()


@curried
def Array_prefix_sums(a):
    return np.cumsum(_ints(a)).tolist()


@curried
def Array_sorted_ascending(a):
    return np.sort(_ints(a)).tolist()


# ── Element-wise zips (two equal-length Array Int -> Array Int) ─────────────


@curried
def Array_zip_plus(a, b):
    n = min(len(a), len(b))
    return (_ints(a)[:n] + _ints(b)[:n]).tolist()


@curried
def Array_zip_minus(a, b):
    return (_ints(a) - _ints(b)).tolist()


@curried
def Array_zip_mul(a, b):
    return (_ints(a) * _ints(b)).tolist()


@curried
def Array_elementwise_max(a, b):
    return np.maximum(_ints(a), _ints(b)).tolist()


@curried
def Array_elementwise_min(a, b):
    return np.minimum(_ints(a), _ints(b)).tolist()
