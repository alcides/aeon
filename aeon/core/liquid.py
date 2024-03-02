from __future__ import annotations

from typing import Sequence


class LiquidTerm:
    pass


def ensure_liqterm(a: LiquidTerm | str) -> LiquidTerm:
    if isinstance(a, str):
        return LiquidVar(a)
    return a


class LiquidHole(LiquidTerm):
    name: str
    argtypes: Sequence[tuple[LiquidTerm, str]]

    def __init__(
        self,
        name: str,
        argtypes: list[tuple[LiquidTerm, str]] | None = None,
    ):
        """To make sure the first element of the argument list is a LiquidVar,
        use (ensure_liqterm(a), b) for (a, b) in argtypes."""
        self.name = name
        self.argtypes = argtypes or []
        assert all(isinstance(a, LiquidVar) for (a, b) in self.argtypes)
        # [(ensure_liqterm(a), b) for (a, b) in (argtypes or [])]

    def __repr__(self):
        j = ", ".join([f"{n}:{t}" for (n, t) in self.argtypes])
        return f"?{self.name}({j})"

    def __eq__(self, other):
        return isinstance(other, LiquidHole) and other.name == self.name

    def __hash__(self) -> int:
        return hash(self.name)


class LiquidLiteralBool(LiquidTerm):
    value: bool

    def __init__(self, value: bool):
        self.value = value

    def __repr__(self):
        return f"{self.value}".lower()

    def __eq__(self, other):
        return isinstance(other, LiquidLiteralBool) and other.value == self.value

    def __hash__(self) -> int:
        return hash(self.value)


class LiquidLiteralInt(LiquidTerm):
    value: int

    def __init__(self, value: int):
        self.value = value

    def __repr__(self):
        return f"{self.value}"

    def __eq__(self, other):
        return isinstance(other, LiquidLiteralInt) and other.value == self.value

    def __hash__(self) -> int:
        return hash(self.value)


class LiquidLiteralFloat(LiquidTerm):
    value: float

    def __init__(self, value: float):
        self.value = value

    def __repr__(self):
        return f"{self.value}"

    def __eq__(self, other):
        return isinstance(other, LiquidLiteralFloat) and other.value == self.value

    def __hash__(self) -> int:
        return hash(self.value)


class LiquidLiteralString(LiquidTerm):
    value: str

    def __init__(self, value: str):
        self.value = value

    def __repr__(self):
        return f"{self.value}"

    def __eq__(self, other):
        return isinstance(other, LiquidLiteralString) and other.value == self.value

    def __hash__(self) -> int:
        return hash(self.value)


class LiquidVar(LiquidTerm):
    name: str

    def __init__(self, name: str):
        assert isinstance(name, str)
        self.name = name

    def __repr__(self):
        return f"{self.name}"

    def __eq__(self, other):
        return isinstance(other, LiquidVar) and other.name == self.name

    def __hash__(self) -> int:
        return hash(self.name)


class LiquidApp(LiquidTerm):
    fun: str
    args: list[LiquidTerm]

    def __init__(self, fun: str, args: list[LiquidTerm]):
        self.fun = fun
        self.args = args
        for a in self.args:
            assert isinstance(a, LiquidTerm)

    def __repr__(self):
        if all([not c.isalnum() for c in self.fun]) and len(self.args) == 2:
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


def liquid_free_vars(e: LiquidTerm) -> list[str]:
    if isinstance(e, LiquidVar):
        return [e.name]
    elif isinstance(e, LiquidApp):
        return [e.fun] + [x for arg in e.args for x in liquid_free_vars(arg)]
    else:
        return []
