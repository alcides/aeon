"""Lifetime and configuration of one compilation, including its dependencies.

Phase-specific state is created lazily, avoiding imports from the leaf session
module back into the compiler. Context-local compatibility state supports the
existing low-level APIs; compilation entrypoints always establish an explicit
session. Sessions are not intended to be shared by concurrent threads.
"""

from __future__ import annotations

from collections.abc import Callable, Iterator, MutableMapping, MutableSet
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field
from functools import wraps
from typing import TYPE_CHECKING, ParamSpec, TypeVar, cast

if TYPE_CHECKING:
    from aeon.errors import AeonError

T = TypeVar("T")
K = TypeVar("K")
V = TypeVar("V")
P = ParamSpec("P")
R = TypeVar("R")


@dataclass(frozen=True)
class CompilationOptions:
    smt_timeout_ms: int = 200
    cache_limit: int = 1024

    def __post_init__(self) -> None:
        if self.smt_timeout_ms <= 0 or self.cache_limit <= 0:
            raise ValueError("SMT timeout and cache limit must be positive")


@dataclass
class CompilationSession:
    options: CompilationOptions = field(default_factory=CompilationOptions)
    diagnostics: list[AeonError] = field(default_factory=list)
    _states: dict[type, object] = field(default_factory=dict, init=False, repr=False)

    def state(self, factory: type[T]) -> T:
        if factory not in self._states:
            with self.activate():
                self._states[factory] = factory()
        return cast(T, self._states[factory])

    @contextmanager
    def activate(self) -> Iterator[CompilationSession]:
        token = _active_session.set(self)
        try:
            yield self
        finally:
            _active_session.reset(token)


_active_session: ContextVar[CompilationSession | None] = ContextVar("aeon_session", default=None)
_compatibility_session: ContextVar[CompilationSession | None] = ContextVar("aeon_compatibility_session", default=None)


def current_session() -> CompilationSession:
    active = _active_session.get()
    if active is not None:
        return active
    session = _compatibility_session.get()
    if session is None:
        session = CompilationSession()
        _compatibility_session.set(session)
    return session


def compilation_entrypoint(function: Callable[P, R]) -> Callable[P, R]:
    """Nested imports share a session; independent top-level calls do not."""

    @wraps(function)
    def wrapped(*args: P.args, **kwargs: P.kwargs) -> R:
        if _active_session.get() is not None:
            return function(*args, **kwargs)
        with CompilationSession().activate():
            return function(*args, **kwargs)

    return wrapped


class SessionMapping(MutableMapping[K, V]):
    """Compatibility view of a dictionary belonging to the active session."""

    def __init__(self, resolve: Callable[[], dict[K, V]]):
        self._resolve = resolve

    def __getitem__(self, key: K) -> V:
        return self._resolve()[key]

    def __setitem__(self, key: K, value: V) -> None:
        self._resolve()[key] = value

    def __delitem__(self, key: K) -> None:
        del self._resolve()[key]

    def __iter__(self) -> Iterator[K]:
        return iter(self._resolve())

    def __len__(self) -> int:
        return len(self._resolve())

    def clear(self) -> None:
        self._resolve().clear()


class SessionSet(MutableSet[T]):
    def __init__(self, resolve: Callable[[], set[T]]):
        self._resolve = resolve

    def __contains__(self, value: object) -> bool:
        return value in self._resolve()

    def __iter__(self) -> Iterator[T]:
        return iter(self._resolve())

    def __len__(self) -> int:
        return len(self._resolve())

    def add(self, value: T) -> None:
        self._resolve().add(value)

    def discard(self, value: T) -> None:
        self._resolve().discard(value)
