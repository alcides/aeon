from z3.z3 import Bool
from aeon.core.types import BaseType, t_int, t_bool
from typing import Any, List, Tuple
from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt, LiquidTerm, LiquidVar
from aeon.verification.vcs import Conjunction, Constraint, Implication, LiquidConstraint
from z3 import Solver, Int, sat, unsat, And, Not

base_functions = {'eq': lambda x, y: x == y}


def smt_valid(c: Constraint) -> bool:
    """ Verifies if a constraint is true using Z3 """
    s = Solver()
    c = translate(c, [])
    s.add(c)
    result = s.check()
    print(s)
    print(result)
    print("...")
    if result == sat:
        return False
    elif result == unsat:
        return True
    else:
        assert False


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


def translate(c: Constraint, variables: List[Tuple[str, Any]]):
    if isinstance(c, LiquidConstraint):
        return translate_liq(c.expr, variables)
    elif isinstance(c, Conjunction):
        e1 = translate(c.c1, variables, variables)
        e2 = translate(c.c2, variables, variables)
        return And(e1, e2)
    elif isinstance(c, Implication):
        nvariables = [(c.name, make_variable(c.name, c.base))] + variables
        e1 = translate_liq(c.pred, nvariables)
        e2 = translate(c.seq, nvariables)
        return And(e1, Not(e2))
