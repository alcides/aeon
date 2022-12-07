from __future__ import annotations

from random import Random
from typing import Any
from typing import List


class RandomSource:

    def next_integer(self) -> int:
        return 0

    def choose(self, options: list[Any]) -> Any:
        assert options
        k = self.next_integer() % len(options)
        return options[k]


class SeededRandomSource(RandomSource):

    def __init__(self, seed):
        self.r = Random()
        self.r.seed(seed)
        self.seed = seed

    def next_integer(self) -> int:
        return self.r.randint(-100000, 100000)

    def __str__(self):
        return f"RandomSource({self.seed})"


class ListRandomSource(RandomSource):
    values: list[int]
    index: int

    def __init__(self, values: list[int]):
        self.values = values
        self.index = 0

    def choose(self, options: list[Any]) -> Any:
        assert options
        k = self.next_integer() % len(options)
        return options[k]

    def next_integer(self) -> int:
        v = self.values[self.index % len(self.values)]
        self.index += 1
        return v

    def __str__(self):
        return str(self.values[self.index:])
