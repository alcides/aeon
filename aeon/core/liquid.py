from __future__ import annotations

from abc import ABC
from dataclasses import dataclass
from aeon.utils.name import Name


class LiquidTerm(ABC):
    pass


def ensure_liqterm(a: LiquidTerm | Name) -> LiquidTerm:
    if isinstance(a, Name):
        return LiquidVar(a)
    return a


class LiquidHole(LiquidTerm):
    def __eq__(self, other):
        return isinstance(other, self.__class__)


def is_safe_for_application(x: LiquidTerm):
    return (
        isinstance(x, LiquidVar)
        or isinstance(x, LiquidLiteralBool)
        or isinstance(x, LiquidLiteralFloat)
        or isinstance(x, LiquidLiteralInt)
        or isinstance(x, LiquidLiteralString)
    )


@dataclass
class LiquidLiteralBool(LiquidTerm):
    value: bool

    def __repr__(self):
        return f"{self.value}".lower()

    def __eq__(self, other):
        return isinstance(other, LiquidLiteralBool) and other.value == self.value

    def __hash__(self) -> int:
        return hash(self.value)


@dataclass
class LiquidLiteralInt(LiquidTerm):
    value: int

    def __repr__(self):
        return f"{self.value}".lower()

    def __eq__(self, other):
        return isinstance(other, LiquidLiteralInt) and other.value == self.value

    def __hash__(self) -> int:
        return hash(self.value)


@dataclass
class LiquidLiteralFloat(LiquidTerm):
    value: float

    def __repr__(self):
        return f"{self.value}".lower()

    def __eq__(self, other):
        return isinstance(other, LiquidLiteralFloat) and other.value == self.value

    def __hash__(self) -> int:
        return hash(self.value)


@dataclass
class LiquidLiteralString(LiquidTerm):
    value: str

    def __repr__(self):
        return f"{self.value}".lower()

    def __eq__(self, other):
        return isinstance(other, LiquidLiteralString) and other.value == self.value

    def __hash__(self) -> int:
        return hash(self.value)


@dataclass
class LiquidVar(LiquidTerm):
    name: Name

    def __repr__(self):
        return f"{self.name}"

    def __eq__(self, other):
        return isinstance(other, LiquidVar) and other.name == self.name

    def __hash__(self) -> int:
        return hash(self.name)


@dataclass
class LiquidApp(LiquidTerm):
    fun: Name
    args: list[LiquidTerm]

    def __repr__(self):
        if all([not c.isalnum() for c in self.fun.name]) and len(self.args) == 2:
            (a1, a2) = (repr(x) for x in self.args)
            return f"({a1} {self.fun} {a2})"

        fargs = ",".join([repr(x) for x in self.args])
        return f"{self.fun}({fargs})"

    def __eq__(self, other):
        return (
            isinstance(other, LiquidApp)
            and other.fun == self.fun
            and all(x == y for (x, y) in zip(self.args, other.args))
        )

    def __hash__(self) -> int:
        return hash(self.fun) + sum(hash(a) for a in self.args)


def liquid_free_vars(e: LiquidTerm) -> list[Name]:
    if isinstance(e, LiquidVar):
        return [e.name]
    elif isinstance(e, LiquidApp):
        return [e.fun] + [x for arg in e.args for x in liquid_free_vars(arg)]
    else:
        return []
