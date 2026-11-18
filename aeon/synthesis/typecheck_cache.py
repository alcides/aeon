"""Bounded, problem-local memoization of complete-program typing results."""

from __future__ import annotations

from collections import OrderedDict
from collections.abc import Callable
from dataclasses import fields, is_dataclass
from enum import Enum
import struct

from aeon.compilation.session import CompilationSession, current_session
from aeon.core.terms import Term
from aeon.core.types import Type, top
from aeon.typechecking.context import TypingContext
from aeon.verification.state import VerificationState


def _typed_key(value: object) -> tuple:
    """Snapshot every semantic field, including fields ignored by AST equality.

    Annotation equality erases its type; Python equality conflates bool/int.
    Neither is suitable for proof reuse. Unknown native payloads bypass caching.
    Snapshot mutable lists/types rather than retaining them as dictionary keys.
    """
    kind = type(value)
    if value is None or kind in (str, bytes, bool, int):
        return kind, value
    if kind is float:
        return kind, struct.pack("!d", value)
    if isinstance(value, Enum):
        return kind, value.name
    if isinstance(value, (list, tuple)):
        return kind, tuple(_typed_key(item) for item in value)
    if isinstance(value, dict):
        return kind, frozenset((_typed_key(k), _typed_key(v)) for k, v in value.items())
    if isinstance(value, (set, frozenset)):
        return kind, frozenset(_typed_key(item) for item in value)
    if is_dataclass(value) and not isinstance(value, type):
        return kind, tuple((f.name, _typed_key(getattr(value, f.name))) for f in fields(value) if f.name != "loc")
    raise TypeError(f"Unsupported typing-cache payload: {kind.__name__}")


class TypecheckingCache:
    """One cache per synthesis validator; runtime specifications stay outside.

    ``compute`` checks the supplied program (possibly naming constructors first)
    at ``expected_type`` in ``ctx``. The key includes the entire unprepared
    program, so changes to surrounding definitions cannot reuse an old proof.
    Sessions, solver resets, timeouts, contexts and expected types also separate
    entries. The cache never normalizes away annotations or refinement arguments.
    """

    def __init__(self, max_entries: int = 256):
        if max_entries < 1:
            raise ValueError("typing cache capacity must be positive")
        self.max_entries = max_entries
        self._session: CompilationSession | None = None
        self._results: OrderedDict[tuple, bool] = OrderedDict()
        self.hits = 0
        self.misses = 0
        self.bypassed = 0
        self.inconclusive = 0

    def check(self, ctx: TypingContext, program: Term, compute: Callable[[], bool], expected_type: Type = top) -> bool:
        session = current_session()
        if session is not self._session:
            self._results.clear()
            self._session = session
        state = session.state(VerificationState)
        try:
            key = (
                state.generation,
                state.timeout_ms,
                _typed_key(tuple(ctx.entries)),
                _typed_key(ctx.trusted_names),
                _typed_key(expected_type),
                _typed_key(program),
            )
        except (TypeError, RecursionError):
            self.bypassed += 1
            return compute()
        if key in self._results:
            self.hits += 1
            self._results.move_to_end(key)
            return self._results[key]
        self.misses += 1
        uncertain_before = state.inconclusive_queries
        result = compute()
        if not result and state.inconclusive_queries != uncertain_before:
            self.inconclusive += 1
            return result
        self._results[key] = result
        if len(self._results) > self.max_entries:
            self._results.popitem(last=False)
        return result
