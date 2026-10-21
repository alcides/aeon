"""Owned contiguous arrays with a shared representation for ranks one to three."""

from __future__ import annotations

import math
from collections.abc import Iterator, Sequence
from typing import Any


def validate_shape(shape: tuple[int, ...]) -> tuple[int, ...]:
    if not 1 <= len(shape) <= 3:
        raise ValueError("NDArray rank must be between one and three")
    if any(isinstance(n, bool) or not isinstance(n, int) or not 0 <= n <= 2**31 - 1 for n in shape):
        raise ValueError("NDArray dimensions must be non-negative 32-bit integers")
    if math.prod(shape) > 2**31 - 1:
        raise ValueError("NDArray element count exceeds Aeon's 32-bit Int range")
    return shape


def contiguous_strides(shape: tuple[int, ...]) -> tuple[int, ...]:
    stride = 1
    strides = []
    for size in reversed(shape):
        strides.append(stride)
        stride *= size
    return tuple(reversed(strides))


class ArrayStorage:
    """Shared ownership of host elements and an optional persistent device copy."""

    def __init__(self, data: list[Any]):
        self.host = data
        self.device: Any = None
        self.host_current = True
        self.version = 0
        self.exposed = False
        self.failure: Exception | None = None

    def read(self) -> list[Any]:
        if self.failure is not None:
            raise RuntimeError("Array storage is unavailable after a GPU execution failure") from self.failure
        if not self.host_current:
            self.device.download(self.host)
            self.host_current = True
        return self.host

    def write(self, values: list[Any]) -> None:
        if self.failure is None and self.host_current and list.__eq__(self.host, values) is True:
            return
        list.__setitem__(self.host, slice(None), values)
        self.version += 1
        self.host_current = True
        self.failure = None

    def expose(self) -> list[Any]:
        values = self.read()
        if isinstance(values, ManagedArray):
            return values
        if not self.exposed and self.device is not None:
            self.device.host_snapshot = tuple(values)
        self.exposed = True
        return values


class ManagedArray(list):
    """A list-compatible Aeon Array with lazy, coherent GPU element storage."""

    def __init__(self, values=()):
        list.__init__(self, values)
        self._storage = ArrayStorage(self)

    def _read(self, method, *args, **kwargs):
        self._storage.read()
        return method(self, *args, **kwargs)

    def _mutate(self, method, *args, **kwargs):
        self._storage.read()
        for value in args:
            if isinstance(value, ManagedArray):
                value._storage.read()
        self._storage.version += 1
        return method(self, *args, **kwargs)

    def __getitem__(self, index):
        value = self._read(list.__getitem__, index)
        return ManagedArray(value) if isinstance(index, slice) else value

    def __setitem__(self, index, value):
        self._mutate(list.__setitem__, index, value)

    def __delitem__(self, index):
        self._mutate(list.__delitem__, index)

    def __iter__(self):
        return self._read(list.__iter__)

    def __reversed__(self):
        return self._read(list.__reversed__)

    def __repr__(self):
        return self._read(list.__repr__)

    __str__ = __repr__

    def __contains__(self, value):
        return self._read(list.__contains__, value)

    def _compare(self, method, other):
        if isinstance(other, ManagedArray):
            other._storage.read()
        return self._read(method, other)

    def __eq__(self, other):
        return self._compare(list.__eq__, other)

    def __ne__(self, other):
        return self._compare(list.__ne__, other)

    def __lt__(self, other):
        return self._compare(list.__lt__, other)

    def __le__(self, other):
        return self._compare(list.__le__, other)

    def __gt__(self, other):
        return self._compare(list.__gt__, other)

    def __ge__(self, other):
        return self._compare(list.__ge__, other)

    def __add__(self, other):
        if isinstance(other, ManagedArray):
            other._storage.read()
        return ManagedArray(self._read(list.__add__, other))

    def __radd__(self, other):
        self._storage.read()
        return ManagedArray(list.__add__(other, self))

    def __mul__(self, value):
        return ManagedArray(self._read(list.__mul__, value))

    __rmul__ = __mul__

    def __iadd__(self, other):
        self._mutate(list.__iadd__, other)
        return self

    def __imul__(self, value):
        self._mutate(list.__imul__, value)
        return self

    def copy(self):
        return ManagedArray(self)

    def count(self, value):
        return self._read(list.count, value)

    def index(self, *args):
        return self._read(list.index, *args)

    def append(self, value):
        self._mutate(list.append, value)

    def extend(self, values):
        self._mutate(list.extend, values)

    def insert(self, index, value):
        self._mutate(list.insert, index, value)

    def pop(self, index=-1):
        return self._mutate(list.pop, index)

    def remove(self, value):
        self._mutate(list.remove, value)

    def reverse(self):
        self._mutate(list.reverse)

    def sort(self, *args, **kwargs):
        self._mutate(list.sort, *args, **kwargs)

    def clear(self):
        self._storage.write([])


class ReadOnlyBuffer(Sequence[Any]):
    """An immutable snapshot handle that can cross GPU calls without downloading."""

    def __init__(self, storage: ArrayStorage):
        self._storage = storage

    def __len__(self) -> int:
        return len(self._storage.host)

    def __getitem__(self, index):
        return self._storage.read()[index]

    def __iter__(self) -> Iterator[Any]:
        return iter(self._storage.read())

    def __repr__(self) -> str:
        return repr(self._storage.read())

    def __eq__(self, other: object) -> bool:
        if isinstance(other, Sequence):
            return list(self) == list(other)
        return NotImplemented


class NDArray:
    """An owned row-major buffer; reshape transfers ownership without copying."""

    def __init__(self, data: list[Any], shape: tuple[int, ...]):
        shape = validate_shape(shape)
        if not isinstance(data, list) or len(data) != math.prod(shape):
            raise ValueError("NDArray shape must match its element count")
        self._storage = data._storage if isinstance(data, ManagedArray) else ArrayStorage(data)
        self._shape = shape
        self._strides = contiguous_strides(shape)
        self._owned = True

    def _check_owned(self) -> None:
        if not self._owned:
            raise ValueError("NDArray ownership has already been transferred")

    @property
    def data(self) -> list[Any]:
        self._check_owned()
        return self._storage.expose()

    def _read_data(self) -> list[Any]:
        self._check_owned()
        return self._storage.read()

    def _write_data(self, values: list[Any]) -> None:
        self._check_owned()
        self._storage.write(values)

    @property
    def shape(self) -> tuple[int, ...]:
        self._check_owned()
        return self._shape

    @property
    def strides(self) -> tuple[int, ...]:
        self._check_owned()
        return self._strides

    @property
    def rank(self) -> int:
        return len(self.shape)

    @property
    def elements(self) -> int:
        return math.prod(self.shape)

    def dimension(self, axis: int) -> int:
        if isinstance(axis, bool) or not isinstance(axis, int) or not 0 <= axis < self.rank:
            raise IndexError("NDArray axis is out of bounds")
        return self.shape[axis]

    def _index(self, indices: tuple[int, ...]) -> int:
        if len(indices) != self.rank:
            raise IndexError("NDArray index rank does not match the array")
        if any(
            isinstance(i, bool) or not isinstance(i, int) or not 0 <= i < size for i, size in zip(indices, self.shape)
        ):
            raise IndexError("NDArray index is out of bounds")
        return sum(i * stride for i, stride in zip(indices, self.strides))

    def get(self, *indices: int) -> Any:
        return self._read_data()[self._index(indices)]

    def set(self, *indices_and_value: Any) -> NDArray:
        indices, value = indices_and_value[:-1], indices_and_value[-1]
        index = self._index(indices)
        values = self._read_data()
        list.__setitem__(values, index, value)
        self._storage.version += 1
        return self

    def fill(self, value: Any) -> NDArray:
        self._write_data([value] * self.elements)
        return self

    def reduce(self, callback: Any, initial: Any) -> Any:
        result = initial
        for value in self._read_data():
            result = callback(result)(value)
        return result

    def map_rows(self, callback: Any) -> NDArray:
        if self.rank != 2:
            raise ValueError("map_rows requires a rank-two NDArray")
        rows, cols = self.shape
        values = self._read_data()
        self._storage.version += 1
        for index in range(rows):
            start = index * cols
            row = NDArray(values[start : start + cols], (cols,))
            result = callback(index)(row)
            if not isinstance(result, NDArray) or result.shape != (cols,):
                raise ValueError("map_rows callback must preserve the row shape")
            values[start : start + cols] = result.to_array()
        return self

    def reshape(self, shape: tuple[int, ...]) -> NDArray:
        self._check_owned()
        shape = validate_shape(shape)
        if math.prod(shape) != self.elements:
            raise ValueError("NDArray shape must match its element count")
        result = NDArray.__new__(NDArray)
        result._storage = self._storage
        result._shape = shape
        result._strides = contiguous_strides(shape)
        result._owned = True
        self._owned = False
        del self._storage
        return result

    def to_1d(self) -> NDArray:
        return self.reshape((self.elements,))

    def from_1d2(self, rows: int, cols: int) -> NDArray:
        if self.rank != 1:
            raise ValueError("from_1d2 requires a rank-one NDArray")
        return self.reshape((rows, cols))

    def from_1d3(self, depth: int, rows: int, cols: int) -> NDArray:
        if self.rank != 1:
            raise ValueError("from_1d3 requires a rank-one NDArray")
        return self.reshape((depth, rows, cols))

    def to_array(self) -> list[Any]:
        if self.rank != 1:
            raise ValueError("to_array requires a rank-one NDArray")
        data = self._storage.host if isinstance(self._storage.host, ManagedArray) else self.data
        self._owned = False
        del self._storage
        return data

    def snapshot(self) -> ReadOnlyBuffer:
        self._check_owned()
        result = ReadOnlyBuffer(self._storage)
        self._owned = False
        del self._storage
        return result

    def discard(self) -> None:
        self._check_owned()
        if self._storage.device is not None:
            self._storage.device.close()
            self._storage.device = None
        self._owned = False
        del self._storage


def from_array(data: list[Any]) -> NDArray:
    return NDArray(data, (len(data),))


def full(shape: tuple[int, ...], value: Any) -> NDArray:
    shape = validate_shape(shape)
    return NDArray([value] * math.prod(shape), shape)
