from typing import Generator

from aeon.core.liquid import (
    LiquidApp,
    LiquidLiteralBool,
    LiquidLiteralInt,
    LiquidTerm,
    LiquidVar,
)
from aeon.core.types import BaseType


class Constraint(object):
    pass


class LiquidConstraint(Constraint):
    expr: LiquidTerm

    def __init__(self, expr: LiquidTerm):
        self.expr = expr

    def __repr__(self):
        return repr(self.expr)


class Conjunction(Constraint):
    c1: Constraint
    c2: Constraint

    def __init__(self, c1: Constraint, c2: Constraint):
        self.c1 = c1
        self.c2 = c2

    def __repr__(self):
        return u"({}) ∧ ({})".format(self.c1, self.c2)


class Implication(Constraint):
    name: str
    base: BaseType
    pred: LiquidTerm
    seq: Constraint

    def __init__(self, name: str, base: BaseType, pred: LiquidTerm,
                 seq: Constraint):
        self.name = name
        self.base = base
        self.pred = pred
        self.seq = seq

    def __repr__(self):
        return u"∀{}:{}, ({}) => {}".format(self.name, self.base, self.pred,
                                            self.seq)


def variables_in_liq(t: LiquidTerm) -> Generator[str, None, None]:
    if isinstance(t, LiquidLiteralBool) or isinstance(t, LiquidLiteralInt):
        pass
    elif isinstance(t, LiquidVar):
        yield t.name
    elif isinstance(t, LiquidApp):
        yield t.fun
        for a in t.args:
            yield from variables_in_liq(a)


def variables_in(c: Constraint) -> Generator[str, None, None]:
    if isinstance(c, Conjunction):
        yield from variables_in(c.c1)
        yield from variables_in(c.c2)
    elif isinstance(c, Implication):
        yield from variables_in_liq(c.pred)
        yield from variables_in(c.seq)
    elif isinstance(c, LiquidConstraint):
        yield from variables_in_liq(c.expr)
