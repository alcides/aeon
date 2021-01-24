from z3.z3 import Bool, And, Not, Or, String
from aeon.core.types import BaseType, t_int, t_bool, t_string
from typing import Any, Dict, Generator, List, Tuple
from aeon.core.liquid import (
    LiquidApp,
    LiquidLiteralBool,
    LiquidLiteralInt,
    LiquidTerm,
    LiquidVar,
)
from aeon.verification.vcs import Conjunction, Constraint, Implication, LiquidConstraint
from z3 import Solver, Int, sat, unsat, And, Not

base_functions: Dict[str, Any] = {
    "==": lambda x, y: x == y,
    "!=": lambda x, y: x != y,
    "<": lambda x, y: x < y,
    "<=": lambda x, y: x <= y,
    ">": lambda x, y: x >= y,
    ">=": lambda x, y: x >= y,
    "!": lambda x: Not(x),
    "+": lambda x, y: x + y,
    "&&": lambda x, y: And(x, y),
    "||": lambda x, y: Or(x, y),
}


class CanonicConstraint(object):
    binders: List[Tuple[str, BaseType]]
    pre: LiquidTerm
    pos: LiquidTerm

    def __init__(self, binders: List[Tuple[str, BaseType]], pre: LiquidTerm,
                 pos: LiquidTerm):
        self.binders = binders
        self.pre = pre
        self.pos = pos

    def __repr__(self):
        return "\\forall {}, {} => {}".format(self.binders, self.pre, self.pos)


def flatten(c: Constraint) -> Generator[CanonicConstraint, None, None]:
    if isinstance(c, Conjunction):
        yield from flatten(c.c1)
        yield from flatten(c.c2)
    elif isinstance(c, Implication):
        for sub in flatten(c.seq):
            yield CanonicConstraint(
                binders=sub.binders + [(c.name, c.base)],
                pre=LiquidApp("&&", [sub.pre, c.pred]),
                pos=sub.pos,
            )
    elif isinstance(c, LiquidConstraint):
        yield CanonicConstraint(binders=[],
                                pre=LiquidLiteralBool(True),
                                pos=c.expr)


def smt_valid_single(c: CanonicConstraint) -> bool:
    s = Solver()
    # print("R2", c, end=" ")
    c = translate(c)
    s.add(c)
    result = s.check()
    # print("<>", s.check() == unsat)
    if result == sat:
        return False
    elif result == unsat:
        return True
    else:
        assert False


def smt_valid(c: Constraint) -> bool:
    """ Verifies if a constraint is true using Z3 """
    cons: List[CanonicConstraint] = list(flatten(c))
    return all([smt_valid_single(c) for c in cons])


def type_of_variable(variables: List[Tuple[str, Any]], name: str) -> Any:
    for (na, ref) in variables:
        if na == name:
            return ref
    assert False


def make_variable(name: str, base: BaseType) -> Any:
    if base == t_int:
        return Int(name)
    elif base == t_bool:
        return Bool(name)
    elif base == t_string:
        return String(name)
    print("NO var:", name, base)
    assert False


def translate_liq(t: LiquidTerm, variables: List[Tuple[str, Any]]):
    if isinstance(t, LiquidLiteralBool):
        return t.value
    elif isinstance(t, LiquidLiteralInt):
        return t.value
    elif isinstance(t, LiquidVar):
        return type_of_variable(variables, t.name)
    elif isinstance(t, LiquidApp):
        args = [translate_liq(a, variables) for a in t.args]
        return base_functions[t.fun](*args)
    assert False


# patterm matching term
"""
def translate_old(c: Constraint, variables: List[Tuple[str, Any]]):
    if isinstance(c, LiquidConstraint):
        return translate_liq(c.expr, variables)
    elif isinstance(c, Conjunction):
        e1 = translate(c.c1, variables)
        e2 = translate(c.c2, variables)
        return And(e1, e2)
    elif isinstance(c, Implication):
        nvariables = [(c.name, make_variable(c.name, c.base))] + variables
        e1 = translate_liq(c.pred, nvariables)
        e2 = translate(c.seq, nvariables)
        return And(e1, Not(e2))
    else:
        assert False
"""


def translate(c: CanonicConstraint):
    variables = [(name, make_variable(name, base))
                 for (name, base) in c.binders if isinstance(base, BaseType)]
    e1 = translate_liq(c.pre, variables)
    e2 = translate_liq(c.pos, variables)
    return And(e1, Not(e2))
