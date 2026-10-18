"""Owned contiguous arrays with a shared representation for ranks one to three."""

from __future__ import annotations

import math
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


class NDArray:
    """An owned row-major buffer; reshape transfers ownership without copying."""

    def __init__(self, data: list[Any], shape: tuple[int, ...]):
        shape = validate_shape(shape)
        if not isinstance(data, list) or len(data) != math.prod(shape):
            raise ValueError("NDArray shape must match its element count")
        self._data = data
        self._shape = shape
        self._strides = contiguous_strides(shape)
        self._owned = True

    def _check_owned(self) -> None:
        if not self._owned:
            raise ValueError("NDArray ownership has already been transferred")

    @property
    def data(self) -> list[Any]:
        self._check_owned()
        return self._data

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
        return len(self.data)

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
        return self.data[self._index(indices)]

    def set(self, *indices_and_value: Any) -> NDArray:
        indices, value = indices_and_value[:-1], indices_and_value[-1]
        self.data[self._index(indices)] = value
        return self

    def fill(self, value: Any) -> NDArray:
        self.data[:] = [value] * self.elements
        return self

    def map_rows(self, callback: Any) -> NDArray:
        if self.rank != 2:
            raise ValueError("map_rows requires a rank-two NDArray")
        rows, cols = self.shape
        for index in range(rows):
            start = index * cols
            row = NDArray(self.data[start : start + cols], (cols,))
            result = callback(index)(row)
            if not isinstance(result, NDArray) or result.shape != (cols,):
                raise ValueError("map_rows callback must preserve the row shape")
            self.data[start : start + cols] = result.to_array()
        return self

    def reshape(self, shape: tuple[int, ...]) -> NDArray:
        self._check_owned()
        result = NDArray(self.data, shape)
        self._owned = False
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
        data = self.data
        self._owned = False
        return data

    def discard(self) -> None:
        self._check_owned()
        self._owned = False


def from_array(data: list[Any]) -> NDArray:
    return NDArray(data, (len(data),))


def full(shape: tuple[int, ...], value: Any) -> NDArray:
    shape = validate_shape(shape)
    return NDArray([value] * math.prod(shape), shape)
