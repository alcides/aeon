from abc import ABC, abstractmethod
from dataclasses import dataclass


class Location(ABC):
    @abstractmethod
    def start(self) -> tuple[int, int]:
        pass

    @abstractmethod
    def end(self) -> tuple[int, int]:
        pass


@dataclass(unsafe_hash=True, frozen=True)
class FileLocation(Location):
    file: str
    start: tuple[int, int]
    end: tuple[int, int]

    def start(self) -> tuple[int, int]:
        return self.start

    def end(self) -> tuple[int, int]:
        return self.end


@dataclass(unsafe_hash=True, frozen=True)
class SynthesizedLocation(Location):
    reason: str

    def start(self) -> tuple[int, int]:
        return 0, 0

    def end(self) -> tuple[int, int]:
        return 0, 0
