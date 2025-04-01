from dataclasses import dataclass, field


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

    def __init__(self, name:str, id=-1):
        assert isinstance(name, str)
        self.name = str(name).strip()
        self.id = id

    def __str__(self):
        return f"{self.name}_{self.id}".replace("-", "neg_")

    def __eq__(self, other):
        return isinstance(other, Name) and self.name == other.name and self.id == other.id


    def __lt__(self, other):
        return self.id < other.id
