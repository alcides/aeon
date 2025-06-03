from abc import ABC
from dataclasses import dataclass


class Location(ABC):
    pass


@dataclass
class FileLocation(Location):
    file: str
    start: tuple[int, int]
    end: tuple[int, int]


@dataclass
class SynthesizedLocation(Location):
    reason: str
