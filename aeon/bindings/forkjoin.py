"""Python bindings for the Aeon ``ForkJoin`` library.

Wraps ``concurrent.futures.ThreadPoolExecutor`` so Aeon programs can fork
independent thunks, join their futures, and shut the pool down. Handle
ownership (exactly-once join / shutdown) is enforced by Aeon linear types in
``ForkJoin.ae``; this module only implements the runtime side.
"""

from __future__ import annotations

from concurrent.futures import Future, ThreadPoolExecutor, wait
from typing import Any, Callable


def pool(workers: int) -> ThreadPoolExecutor:
    """Create a thread pool with a positive worker count."""
    return ThreadPoolExecutor(max_workers=workers)


def fork(pool_: ThreadPoolExecutor, task: Callable[[Any], Any]) -> tuple[ThreadPoolExecutor, Future[Any]]:
    """Submit ``task`` (an Aeon ``Unit -> a`` thunk) and return ``(pool, future)``."""
    future = pool_.submit(task, None)
    return (pool_, future)


def fork2(
    pool_: ThreadPoolExecutor,
    left: Callable[[Any], Any],
    right: Callable[[Any], Any],
) -> tuple[ThreadPoolExecutor, Future[Any], Future[Any]]:
    """Submit two independent thunks; return ``(pool, left_future, right_future)``."""
    fl = pool_.submit(left, None)
    fr = pool_.submit(right, None)
    return (pool_, fl, fr)


def invoke(pool_: ThreadPoolExecutor, task: Callable[[Any], Any]) -> tuple[ThreadPoolExecutor, Any]:
    """Run ``task`` on the pool and wait; return ``(pool, result)``."""
    result = pool_.submit(task, None).result()
    return (pool_, result)


def join(future: Future[Any]) -> Any:
    """Block until ``future`` completes and return its result."""
    return future.result()


def join_timeout(seconds: float, future: Future[Any]) -> Any:
    """Like :func:`join` but abort after a positive ``seconds`` timeout."""
    return future.result(timeout=seconds)


def join2(left: Future[Any], right: Future[Any]) -> tuple[Any, Any]:
    """Wait for both futures (in parallel completion order) and return ``(left, right)``."""
    wait((left, right))
    return (left.result(), right.result())


def shutdown(pool_: ThreadPoolExecutor) -> None:
    """Shut the pool down, waiting for in-flight work. Consumes the pool handle."""
    pool_.shutdown(wait=True)
    return None


def parallel2(
    workers: int,
    left: Callable[[Any], Any],
    right: Callable[[Any], Any],
) -> tuple[Any, Any]:
    """One-shot: create a pool, run two thunks in parallel, join, shut down."""
    with ThreadPoolExecutor(max_workers=workers) as ex:
        fl = ex.submit(left, None)
        fr = ex.submit(right, None)
        wait((fl, fr))
        return (fl.result(), fr.result())


def par_map(workers: int, f: Callable[[Any], Any], xs: list[Any]) -> list[Any]:
    """Map ``f`` over ``xs`` with a temporary pool; length is preserved."""
    with ThreadPoolExecutor(max_workers=workers) as ex:
        return list(ex.map(f, xs))


def halves(xs: list[Any]) -> tuple[list[Any], list[Any]]:
    """Split a non-trivial array into two non-empty contiguous halves."""
    mid = len(xs) // 2
    return (xs[:mid], xs[mid:])
