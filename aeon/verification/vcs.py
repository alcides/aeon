from __future__ import annotations

from dataclasses import dataclass
from typing import Generator

from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidLiteralString
from aeon.core.liquid import LiquidTerm
from aeon.core.liquid import LiquidVar
from aeon.core.types import AbstractionType, Top, TypeVar
from aeon.core.types import BaseType


class Constraint:
    pass


@dataclass
class LiquidConstraint(Constraint):
    expr: LiquidTerm

    def __repr__(self):
        return repr(self.expr)


@dataclass
class Conjunction(Constraint):
    c1: Constraint
    c2: Constraint

    def __repr__(self):
        return f"({self.c1}) ∧ ({self.c2})"


@dataclass
class UninterpretedFunctionDeclaration(Constraint):
    name: str
    type: AbstractionType
    seq: Constraint

    def __repr__(self):
        return f"fun {self.name}:{self.type} => {self.seq}"


@dataclass
class Implication(Constraint):
    name: str
    base: BaseType | TypeVar | Top
    pred: LiquidTerm
    seq: Constraint

    def __repr__(self):
        return f"∀{self.name}:{self.base}, ({self.pred}) => {self.seq}"


@dataclass
class TypeVarDeclaration(Constraint):
    name: str
    seq: Constraint

    def __repr__(self):
        return f"type {self.name}, {self.seq}"


def variables_in_liq(t: LiquidTerm) -> Generator[str, None, None]:
    if isinstance(t, LiquidLiteralBool) or isinstance(
            t, LiquidLiteralInt) or isinstance(t, LiquidLiteralString):
        pass
    elif isinstance(t, LiquidVar):
        yield t.name
    elif isinstance(t, LiquidApp):
        yield t.fun
        for a in t.args:
            yield from variables_in_liq(a)


def variables_free_in(c: Constraint) -> Generator[str, None, None]:
    if isinstance(c, Conjunction):
        yield from variables_free_in(c.c1)
        yield from variables_free_in(c.c2)
    elif isinstance(c, Implication):
        for k in variables_in_liq(c.pred):
            if k != c.name:
                yield k
        for k in variables_free_in(c.seq):
            if k != c.name:
                yield k
    elif isinstance(c, LiquidConstraint):
        yield from variables_in_liq(c.expr)
