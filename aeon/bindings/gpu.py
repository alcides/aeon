"""Python bindings for the Aeon ``Gpu`` library.

GPU primitives are exposed only when the ``Gpu`` module is imported (explicitly
via ``open Gpu`` or automatically by the ``@gpu`` decorator).
"""

from __future__ import annotations


def gpu_map(f):
    def run(t, conf=None):
        # TODO add gpu support
        return [f(x) for x in t]

    return run


def gpu_imap(f):
    def run(t, conf=None):
        # TODO add gpu support
        return [f(i) for i in range(len(t))]

    return run


def gpu_reduce(f):
    def with_initial(i):
        def run(t, conf=None):
            import functools

            # TODO add gpu support
            return functools.reduce(lambda x, y: f(x)(y), t, i)

        return run

    return with_initial


def gpu_filter(f):
    def run(t, conf=None):
        # TODO add gpu support
        return [x for x in t if f(x)]

    return run


def gpu_dot(a):
    def with_b(b):
        # TODO add gpu support
        return sum(x * y for x, y in zip(a, b))

    return with_b


def gpu_run(k):
    def with_config(c):
        def with_input(t):
            print(f"Executing kernel on CPU (for now) with config {c}...")
            return k(t)

        return with_input

    return with_config
