"""Shared ordered map storage for typing-context binding indexes.

Values remain shared objects, like a shallow dict/list copy. Only container
structure is persistent; no typechecking or proof result is cached here.
"""

from __future__ import annotations

from collections.abc import Iterable, Iterator, Mapping
from itertools import chain
from typing import Generic, TypeVar

K = TypeVar("K")
V = TypeVar("V")
T = TypeVar("T")


class PersistentSequence(Generic[T]):
    __slots__ = ("_blocks", "_tail", "_length")
    _CHUNK = 32

    def __init__(self, values: Iterable[T] = ()) -> None:
        items = tuple(values)
        boundary = len(items) // self._CHUNK * self._CHUNK
        self._blocks = tuple(items[i : i + self._CHUNK] for i in range(0, boundary, self._CHUNK))
        self._tail = items[boundary:]
        self._length = len(items)

    def append(self, value: T) -> PersistentSequence[T]:
        result: PersistentSequence[T] = object.__new__(type(self))
        tail = (*self._tail, value)
        result._blocks, result._tail = ((*self._blocks, tail), ()) if len(tail) == self._CHUNK else (self._blocks, tail)
        result._length = self._length + 1
        return result

    def __iter__(self) -> Iterator[T]:
        return chain(chain.from_iterable(self._blocks), self._tail)

    def __len__(self) -> int:
        return self._length


class PersistentMap(Mapping[K, V]):
    """Insertion-ordered map copying only one of 32 hash buckets per update.

    Iteration order matches dict, including updates to an existing key. Keys
    must be immutable. Child binding indexes share all unchanged buckets.
    """

    __slots__ = ("_buckets", "_keys")
    _BUCKETS = 32

    def __init__(self, values: Mapping[K, V] | None = None) -> None:
        flat = {} if values is None else dict(values)
        buckets: tuple[dict[K, V], ...] = tuple({} for _ in range(self._BUCKETS))
        for key, value in flat.items():
            buckets[hash(key) % self._BUCKETS][key] = value
        self._buckets = buckets
        self._keys: PersistentSequence[K] = PersistentSequence(flat)

    def set(self, key: K, value: V) -> PersistentMap[K, V]:
        position = hash(key) % self._BUCKETS
        bucket = self._buckets[position]
        result: PersistentMap[K, V] = object.__new__(type(self))
        result._keys = self._keys if key in bucket else self._keys.append(key)
        result._buckets = (*self._buckets[:position], {**bucket, key: value}, *self._buckets[position + 1 :])
        return result

    def __getitem__(self, key: K) -> V:
        return self._buckets[hash(key) % self._BUCKETS][key]

    def get(self, key, default=None):
        return self._buckets[hash(key) % self._BUCKETS].get(key, default)

    def __contains__(self, key: object) -> bool:
        return key in self._buckets[hash(key) % self._BUCKETS]

    def __iter__(self) -> Iterator[K]:
        return iter(self._keys)

    def __len__(self) -> int:
        return len(self._keys)

    def __reduce__(self):
        # String hashes vary across Python processes. Rebuild buckets in the
        # receiver instead of serializing their process-local positions.
        return type(self), (dict(self),)
