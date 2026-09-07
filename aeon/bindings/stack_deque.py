"""Runtime helpers for ``libraries/Stack.ae`` and ``libraries/Deque.ae``."""

from __future__ import annotations

from collections import deque


def new_stack():
    return []


def stack_push(x, stack):
    stack.append(x)
    return stack


def stack_pop(stack):
    return (stack.pop(), stack)


def stack_peek(stack):
    return (stack[-1], stack)


def new_deque():
    return deque()


def deque_push_back(x, d):
    d.append(x)
    return d


def deque_push_front(x, d):
    d.appendleft(x)
    return d


def deque_pop_back(d):
    return (d.pop(), d)


def deque_pop_front(d):
    return (d.popleft(), d)


def deque_peek_back(d):
    return (d[-1], d)


def deque_peek_front(d):
    return (d[0], d)
