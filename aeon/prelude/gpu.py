"""GPU-shaped helpers, implemented as CPU fallbacks for now.

These were originally in :mod:`aeon.prelude.prelude` and pulled into every
synthesis context. They're moved here so that programs only see them when
they explicitly ``open Gpu`` / ``import Gpu`` (which loads
``libraries/Gpu.ae``, in turn importing this module via ``native_import``).
"""

from __future__ import annotations

import functools


def index_tensor(t):
    def at(i):
        return t[i]

    return at


def gpu_map(f):
    def run(t, conf=None):
        return [f(x) for x in t]

    return run


def gpu_imap(f):
    def run(t, conf=None):
        return [f(i) for i in range(len(t))]

    return run


def gpu_reduce(f):
    def with_initial(i):
        def run(t, conf=None):
            return functools.reduce(lambda x, y: f(x)(y), t, i)

        return run

    return with_initial


def gpu_filter(f):
    def run(t, conf=None):
        return [x for x in t if f(x)]

    return run


def gpu_dot(a):
    def with_b(b):
        return sum(x * y for x, y in zip(a, b))

    return with_b


def gpu_run(k):
    def with_config(c):
        def with_input(t):
            return k(t)

        return with_input

    return with_config
