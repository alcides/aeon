from __future__ import annotations

import functools


def curried(x, argc=None):
    if argc is None:
        argc = x.__code__.co_argcount

    def p(*a):
        if len(a) == argc:
            return x(*a)

        def q(*b):
            return x(*(a + b))

        return curried(q, argc - len(a))

    return p
