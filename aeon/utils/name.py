from dataclasses import dataclass, field

from aeon.utils.superscripts import superscript


class FreshCounter:
    counter: int

    def __init__(self):
        self.counter = 0

    def fresh(self) -> int:
        self.counter += 1
        return self.counter


fresh_counter = FreshCounter()


@dataclass(init=False, unsafe_hash=True)
class Name:
    name: str
    id: int = field(default=-1)

    def __init__(self, name: str, id=-1):
        assert isinstance(name, str)
        self.name = str(name).strip()
        self.id = id

    def __str__(self):
        if self.id == 0:
            return self.name
        elif self.id == -1:
            return f"{self.name}?"
        else:
            return f"{self.name}{superscript(str(self.id))}"

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        return isinstance(other, Name) and self.name == other.name and self.id == other.id

    def __lt__(self, other):
        return self.id < other.id
