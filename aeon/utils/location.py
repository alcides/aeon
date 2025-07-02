from abc import ABC
from dataclasses import dataclass


class Location(ABC):
    pass


@dataclass(unsafe_hash=True, frozen=True)
class FileLocation(Location):
    file: str
    start: tuple[int, int]
    end: tuple[int, int]


@dataclass(unsafe_hash=True, frozen=True)
class SynthesizedLocation(Location):
    reason: str
